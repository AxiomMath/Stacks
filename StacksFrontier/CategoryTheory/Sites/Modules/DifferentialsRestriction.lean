module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialsRepresentable
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PrincipalPartsUniversal
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.QuasicoherentAlgebras
public import StacksFrontier.CategoryTheory.Sites.Modules.Differentials
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DenseSubsiteSheafification
public import StacksFrontier.CategoryTheory.Sites.Modules.Flat
public import StacksFrontier.CategoryTheory.Sites.Modules.DifferentialsSheafification
import StacksCore.Tactic.StacksAttribute

/-!
# Restriction of the sheaf of relative differentials along a functor of sites

Let `G : C ⥤ D` be a continuous and cocontinuous functor of small sites `(C, J)` and `(D, K)`,
and let `φ : O₁ ⟶ O₂` be a homomorphism of sheaves of commutative rings on `(D, K)`.
Restriction of sections along `G` carries `O₂`-modules to modules over the restricted sheaf of
rings, and this file proves that it carries the sheaf of relative differentials to the sheaf of
relative differentials of the restricted homomorphism:

`G^{-1}Ω_{O₂/O₁} ≅ Ω_{G^{-1}O₂/G^{-1}O₁}`,

compatibly with the universal derivations. The same argument gives the companion statement for
the tensor product of sheaves of modules,

`G^{-1}(M ⊗_{O₂} N) ≅ G^{-1}M ⊗_{G^{-1}O₂} G^{-1}N`,

which is what the first term of a sequence of first principal parts needs.

The content is that **restriction along `G` commutes with the sheafification occurring in `Ω`**.
`Stacks.Sheaves.Differentials.moduleOfDifferentials` is the sheafification of the presheaf of
sectionwise Kähler differentials, and the restriction of that presheaf along `G` is the presheaf
of sectionwise Kähler differentials of the restricted homomorphism — on the nose, by
`Stacks.Sheaves.Differentials.presheafPushforward_relativeDifferentials`. So the whole statement
is
`Stacks.SheafOfModules.PushforwardSheafification.pushforwardSheafifyIso` — sheafification of
presheaves of modules commutes with restriction along a continuous and cocontinuous functor —
read at that one presheaf. Nothing about sheafification is reproved here.

This is **not** [Stacks, Tag 08TQ]. That lemma, which is
`Stacks.Sheaves.Differentials.pullbackDifferentialsIso`, is about the *inverse image*
`f^{-1} = G.sheafPullback` of a morphism of topoi presented by `G`, which is the left adjoint of
the restriction appearing here; for a cocontinuous `G` the restriction is itself the inverse
image of a morphism of topoi in the other direction, and that is the morphism whose statement
this is.

## Main definitions

* `Stacks.Sheaves.Differentials.restrictedCommRing` and `restrictedCommRingMap`: `G^{-1}O` and
  `G^{-1}φ`, the restrictions along `G` of a sheaf of commutative rings and of a homomorphism.
* `Stacks.Sheaves.Differentials.restrictDerivation`: a relative derivation restricted along `G`,
  which is the derivation read at the objects `G V`.
* `Stacks.Sheaves.Differentials.restrictedDifferentialsIso`:
  **`G^{-1}Ω_{O₂/O₁} ≅ Ω_{G^{-1}O₂/G^{-1}O₁}`**, and
  `Stacks.Sheaves.Differentials.restrictedDifferentialsOfSiteIso`, the same at the
  corepresenting-object spelling of `Ω`, which is the one the sequence of first principal parts
  and the Atiyah triangle are formed in.
* `Stacks.Sheaves.Differentials.presheafRestrictedModules`: restriction of presheaves of modules
  along `G`, with the body and the result type the tensor-product assembly needs.
* `Stacks.Sheaves.Differentials.restrictedSheafTensorRightIso`:
  **`G^{-1}(M ⊗_{O₂} N) ≅ G^{-1}M ⊗_{G^{-1}O₂} G^{-1}N`.**

## Main results

* `Stacks.Sheaves.Differentials.presheafPushforward_relativeDifferentials`: the presheaf of
  sectionwise Kähler differentials restricted along `G` **is** the presheaf of sectionwise
  Kähler differentials of `G^{-1}φ`, by `rfl`.
* `Stacks.Sheaves.Differentials.restrictedDifferentialsIso_inv_universalDerivation` and
  `homEquiv_restrictedDifferentialsOfSiteIso_hom`: the comparison carries the universal
  derivation of `G^{-1}φ` to the restriction of the universal derivation of `φ`. This pins the
  isomorphism down, so it is *the* canonical identification and not merely some isomorphism
  between the two sheaves.
* `Stacks.Sheaves.Differentials.moduleOfDifferentialsCorepresentableBy` and
  `moduleOfDifferentialsIsoOfSite`: the sheafification spelling of `Ω` corepresents relative
  derivations, hence agrees with the corepresenting-object spelling.
* `Stacks.Sheaves.Differentials.tensorRight_comp_presheafRestrictedModules` and
  `forget_tensorRight_comp_presheafRestrictedModules`: the objectwise tensor product commutes
  with restriction along `G`, and the assembly of that `rfl` into the shape the sheafification
  comparison composes with.

## Implementation notes

**One spelling for the restricted sheaf of rings.** The sheaf of rings indexing the restricted
modules has two spellings: `Stacks.SheafOfModules.PushforwardSheafification.pushforwardRingSheaf`
of the underlying sheaf of rings of `O₂`, which is what the sheafification comparison produces,
and `Stacks.Sheaves.Differentials.underlyingRingSheaf` of `G^{-1}O₂`, which is what
`moduleOfDifferentials` of the restricted homomorphism is indexed by. The two are definitionally
equal — both are `G.op ⋙ O₂.obj ⋙ forget₂ _ _`, with a proof-irrelevant sheaf condition — and
`restrictedDifferentialsIso` is therefore that comparison with its type ascribed; no
transport and no `eqToIso` appears. The ascription is written out rather than inferred because
instance search does not unfold `CategoryTheory.sheafCompose`.

**The tensor product, and why the `rfl`s there are assembled rather than asked for in one
piece.** The tensor product of sheaves of modules is the objectwise one followed by
sheafification, so `restrictedSheafTensorRightIso` has the same one-line content as
`restrictedDifferentialsIso` — but asking `rfl` for the composite exhausts the heartbeat budget
while each of its three steps is cheap. The remedy is the recipe set out in the implementation
notes of `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/DenseSubsiteSheafTensor.lean`, which is
the same assembly for a dense subsite inclusion and a different tensor spelling: pin each
spelling with a declared result type, ask `rfl` one small question at a time, and whisker the
remaining step with `congrArg`. No elaboration option is set and no heartbeat budget is raised
here.

**Universes.** The two sites are small in one universe `u`, which is the universe of the
sections of the sheaves of rings and of the modules. This is
`Stacks.Sheaves.Differentials.moduleOfDifferentials`' own generality and not a narrowing: the
sectionwise Kähler differentials of a `CommRingCat.{u}`-valued sheaf of rings are `u`-sized.

## References

* [Stacks Project, Tag 04BL](https://stacks.math.columbia.edu/tag/04BL), the corepresentability
  of relative derivations, whose representing object is restricted here.
* [Stacks Project, Tag 08TP](https://stacks.math.columbia.edu/tag/08TP), the description of
  `Ω` as the sheafification of the sectionwise Kähler differentials.
-/

@[expose] public noncomputable section

open CategoryTheory Limits
open Stacks.SheafOfModules.PushforwardSheafification (pushforwardRingSheaf
  presheafPushforwardFunctor sheafPushforwardFunctor pushforwardUnit pushforwardSheafifyHom
  pushforwardSheafifyIso)

attribute [local instance_reducible] CategoryTheory.sheafCompose

universe u

namespace Stacks.Sheaves.Differentials

variable {C : Type u} [SmallCategory C] {D : Type u} [SmallCategory D]
  (J : GrothendieckTopology C) {K : GrothendieckTopology D} (G : C ⥤ D)
  [G.IsContinuous J K] [G.IsCocontinuous J K]
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  {O₁ O₂ : Sheaf K CommRingCat.{u}} (φ : O₁ ⟶ O₂)

/-- `G^{-1}O`, the restriction of a sheaf of commutative rings along `G`. -/
abbrev restrictedCommRing (O : Sheaf K CommRingCat.{u}) : Sheaf J CommRingCat.{u} :=
  (G.sheafPushforwardContinuous CommRingCat.{u} J K).obj O

/-- `G^{-1}φ`, the restriction along `G` of a homomorphism of sheaves of commutative rings. -/
abbrev restrictedCommRingMap :
    restrictedCommRing J G O₁ ⟶ restrictedCommRing J G O₂ :=
  (G.sheafPushforwardContinuous CommRingCat.{u} J K).map φ

omit [G.IsCocontinuous J K] [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
  [K.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- **The presheaf of sectionwise Kähler differentials restricted along `G` is the presheaf of
sectionwise Kähler differentials of the restricted homomorphism.** Both have `Ω[O₂(G V)⁄O₁(G V)]`
as sections over `V` and restrict along `G f`; nothing happens, and the two are equal. -/
theorem presheafPushforward_relativeDifferentials :
    (presheafPushforwardFunctor.{u} J G (Stacks.SheafOfModules.Tensor.ringSheaf O₂)).obj
        (PresheafOfModulesOfCommRing.DifferentialsConstruction.relativeDifferentials' φ.hom) =
      PresheafOfModulesOfCommRing.DifferentialsConstruction.relativeDifferentials'
        (restrictedCommRingMap J G φ).hom :=
  rfl

/-- **Restriction of sheaves of modules along `G`**, with no change of scalars: the restriction
functor of
`Stacks.SheafOfModules.PushforwardSheafification.sheafPushforwardFunctor`, with its target
ascribed to the sheaf of rings `Ω` of the restricted homomorphism is indexed by. The two
spellings of that sheaf of rings are definitionally equal; the ascription is what lets the two
sides of `Stacks.Sheaves.Differentials.restrictedDifferentialsIso` be stated together. -/
abbrev restrictedModules :
    SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₂) ⥤
      SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (restrictedCommRing J G O₂)) :=
  sheafPushforwardFunctor.{u} J G (Stacks.SheafOfModules.Tensor.ringSheaf O₂)

/-- **A relative derivation restricted along `G`**: the same additive maps, read only at the
objects `G V`. The Leibniz rule, the compatibility with restriction and the vanishing on the
base are the original ones, the restriction maps of the restricted presheaves being the
restriction maps of the original ones along `G`. -/
def restrictDerivation {M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₂)}
    (d : PresheafOfModulesOfCommRing.Derivation' M.val φ.hom) :
    PresheafOfModulesOfCommRing.Derivation' ((restrictedModules J G (O₂ := O₂)).obj M).val
      (restrictedCommRingMap J G φ).hom where
  d {V} := d.d (X := G.op.obj V)
  d_mul a b := d.d_mul a b
  d_map f x := d.d_map (G.op.map f) x
  d_app a := d.d_app a

omit [G.IsCocontinuous J K] [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
  [K.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- On a section `b` over `V`, the restricted derivation `restrictDerivation J G φ d` is `d`
evaluated at `b`, viewed as a section over `G V`. -/
theorem restrictDerivation_d {M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₂)}
    (d : PresheafOfModulesOfCommRing.Derivation' M.val φ.hom) {V : Cᵒᵖ}
    (b : (restrictedCommRing J G O₂).obj.obj V) :
    (restrictDerivation J G φ d).d b = d.d b :=
  rfl

/-- **`G^{-1}Ω_{O₂/O₁} ≅ Ω_{G^{-1}O₂/G^{-1}O₁}`.** Restriction along a continuous and
cocontinuous functor of sites carries the sheaf of relative differentials to the sheaf of
relative differentials of the restricted homomorphism.

Both sides are sheafifications of one and the same presheaf of modules — the presheaf of
sectionwise Kähler differentials, restricted along `G`, by
`Stacks.Sheaves.Differentials.presheafPushforward_relativeDifferentials` — so this is
`Stacks.SheafOfModules.PushforwardSheafification.pushforwardSheafifyIso` read at that
presheaf. -/
def restrictedDifferentialsIso :
    (restrictedModules J G (O₂ := O₂)).obj (moduleOfDifferentials O₁ O₂ φ) ≅
      moduleOfDifferentials (restrictedCommRing J G O₁) (restrictedCommRing J G O₂)
        (restrictedCommRingMap J G φ) :=
  (pushforwardSheafifyIso.{u} J G (Stacks.SheafOfModules.Tensor.ringSheaf O₂)
    (PresheafOfModulesOfCommRing.DifferentialsConstruction.relativeDifferentials' φ.hom)).symm

/-- **The comparison carries the universal derivation of `G^{-1}φ` to the restriction of the
universal derivation of `φ`**, which is the equation that pins it down: by the corepresentability
of relative derivations there is exactly one morphism doing this. -/
theorem restrictedDifferentialsIso_inv_universalDerivation :
    (universalDerivation (restrictedCommRing J G O₁) (restrictedCommRing J G O₂)
          (restrictedCommRingMap J G φ)).postcomp
        (restrictedDifferentialsIso J G φ).inv.val =
      restrictDerivation J G φ (universalDerivation O₁ O₂ φ) := by
  have h : PresheafOfModules.sheafificationHomEquiv
        (𝟙 (pushforwardRingSheaf J G (Stacks.SheafOfModules.Tensor.ringSheaf O₂)).obj)
        (pushforwardSheafifyHom.{u} J G (Stacks.SheafOfModules.Tensor.ringSheaf O₂)
          (PresheafOfModulesOfCommRing.DifferentialsConstruction.relativeDifferentials' φ.hom)) =
      pushforwardUnit.{u} J G (Stacks.SheafOfModules.Tensor.ringSheaf O₂)
        (PresheafOfModulesOfCommRing.DifferentialsConstruction.relativeDifferentials' φ.hom) :=
    Equiv.apply_symm_apply _ _
  exact congrArg (fun m => (PresheafOfModulesOfCommRing.DifferentialsConstruction.derivation'
    (restrictedCommRingMap J G φ).hom).postcomp m) h

/-! ### The same, at the corepresenting-object spelling of `Ω` -/

section OfSite

open AlgebraicGeometry.SheafOfModules (derivationsFunctor moduleOfDifferentialsOfSite
  universalDerivationOfSite universalDerivationCorepresentableBy corepresentableByIso)

/-- **The sheafification spelling of `Ω` corepresents relative derivations.** This is
`Stacks.Sheaves.Differentials.universalDerivation_isUniversal` — Stacks 04BL in
unique-factorization form — packaged as a corepresentation, which is what compares it with the
corepresenting object `AlgebraicGeometry.SheafOfModules.moduleOfDifferentialsOfSite`. The
ringed-space analogue is
`Stacks.Sheaves.RingedSpaceCotangent.moduleOfDifferentials_corepresentableBy`; here the site is
an arbitrary small one, which is the generality
`Stacks.Sheaves.Differentials.moduleOfDifferentials` is stated in, and all four universe
parameters of the corepresentation collapse to the single universe `u` of that statement. -/
def moduleOfDifferentialsCorepresentableBy {E : Type u} [SmallCategory E]
    {L : GrothendieckTopology E} [L.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    (O₁ O₂ : Sheaf L CommRingCat.{u}) (φ : O₁ ⟶ O₂) :
    (derivationsFunctor.{u} O₁ O₂ φ).CorepresentableBy (moduleOfDifferentials O₁ O₂ φ) :=
  universalDerivationCorepresentableBy.{u, u, u, u} O₁ O₂ φ (universalDerivation O₁ O₂ φ)
    (universalDerivation_isUniversal O₁ O₂ φ)

/-- **The two spellings of `Ω` on a small site agree.** The sheafification of the sectionwise
Kähler differentials and the chosen corepresenting object of the derivations functor are
isomorphic, both corepresenting that functor. -/
def moduleOfDifferentialsIsoOfSite {E : Type u} [SmallCategory E]
    {L : GrothendieckTopology E} [L.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    (O₁ O₂ : Sheaf L CommRingCat.{u}) (φ : O₁ ⟶ O₂) :
    moduleOfDifferentials O₁ O₂ φ ≅ moduleOfDifferentialsOfSite.{u, u, u, u} O₁ O₂ φ :=
  (moduleOfDifferentialsCorepresentableBy O₁ O₂ φ).isoCoreprX

/-- **The restriction of `Ω_{O₂/O₁}` along `G` corepresents the `G^{-1}O₁`-derivations of
`G^{-1}O₂`.** This is `Stacks.Sheaves.Differentials.restrictedDifferentialsIso` read through
the corepresentation of the sheafification spelling. -/
def restrictedDifferentialsOfSiteCorepresentableBy :
    (derivationsFunctor.{u} (restrictedCommRing J G O₁) (restrictedCommRing J G O₂)
        (restrictedCommRingMap J G φ)).CorepresentableBy
      ((restrictedModules J G (O₂ := O₂)).obj
        (moduleOfDifferentialsOfSite.{u, u, u, u} O₁ O₂ φ)) :=
  (moduleOfDifferentialsCorepresentableBy (restrictedCommRing J G O₁)
    (restrictedCommRing J G O₂) (restrictedCommRingMap J G φ)).ofIsoObj
      ((restrictedModules J G (O₂ := O₂)).mapIso
        (moduleOfDifferentialsIsoOfSite O₁ O₂ φ).symm ≪≫ restrictedDifferentialsIso J G φ)

/-- **`G^{-1}Ω_{O₂/O₁} ≅ Ω_{G^{-1}O₂/G^{-1}O₁}` at the corepresenting-object spelling of `Ω`**,
which is the spelling in which the sequence of first principal parts and the Atiyah triangle are
formed. -/
def restrictedDifferentialsOfSiteIso :
    (restrictedModules J G (O₂ := O₂)).obj
        (moduleOfDifferentialsOfSite.{u, u, u, u} O₁ O₂ φ) ≅
      moduleOfDifferentialsOfSite.{u, u, u, u} (restrictedCommRing J G O₁)
        (restrictedCommRing J G O₂) (restrictedCommRingMap J G φ) :=
  corepresentableByIso (restrictedDifferentialsOfSiteCorepresentableBy J G φ)
    (derivationsFunctor.{u} (restrictedCommRing J G O₁) (restrictedCommRing J G O₂)
      (restrictedCommRingMap J G φ)).corepresentableBy

/-- **The identification is the one carrying the restricted universal derivation to the
universal derivation.** Transposing it along the corepresentation of
`Stacks.Sheaves.Differentials.restrictedDifferentialsOfSiteCorepresentableBy` returns the
universal derivation of `G^{-1}φ`, and by corepresentability no other morphism does. -/
theorem homEquiv_restrictedDifferentialsOfSiteIso_hom :
    (restrictedDifferentialsOfSiteCorepresentableBy J G φ).homEquiv
        (restrictedDifferentialsOfSiteIso J G φ).hom =
      universalDerivationOfSite.{u, u, u, u} (restrictedCommRing J G O₁)
        (restrictedCommRing J G O₂) (restrictedCommRingMap J G φ) :=
  (restrictedDifferentialsOfSiteCorepresentableBy J G φ).homEquiv.apply_symm_apply _

end OfSite

/-! ### Restriction and the tensor product of sheaves of modules -/

section Tensor


/-- **Restriction of presheaves of modules along `G`**, `PresheafOfModules.pushforward₀ G`, with
values in presheaves of modules over the ring presheaf of the restricted sheaf of rings.

Implementation note: it is `PresheafOfModules.pushforward₀` rather than
`PresheafOfModules.pushforward (𝟙 _)`, so that it commutes with the objectwise tensor product by
`rfl`. -/
abbrev presheafRestrictedModules :
    PresheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₂).obj ⥤
      PresheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (restrictedCommRing J G O₂)).obj :=
  PresheafOfModules.pushforward₀ G (Stacks.SheafOfModules.Tensor.ringSheaf O₂).obj

omit [G.IsCocontinuous J K] [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
  [K.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- Forgetting a sheaf of modules to a presheaf and then restricting is restricting and then
forgetting. -/
theorem forget_comp_presheafRestrictedModules :
    SheafOfModules.forget.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₂) ⋙
        presheafRestrictedModules J G (O₂ := O₂) =
      restrictedModules J G (O₂ := O₂) ⋙
        SheafOfModules.forget.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf (restrictedCommRing J G O₂)) :=
  rfl

omit [G.IsCocontinuous J K] [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
  [K.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- **The objectwise tensor product commutes with restriction along `G`.** -/
theorem tensorRight_comp_presheafRestrictedModules
    (N : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₂)) :
    _root_.AlgebraicGeometry.SheafOfModules.PresheafOfModules.tensorRight (O := O₂.obj) N.val ⋙
        presheafRestrictedModules J G (O₂ := O₂) =
      presheafRestrictedModules J G (O₂ := O₂) ⋙
        _root_.AlgebraicGeometry.SheafOfModules.PresheafOfModules.tensorRight
          (O := (restrictedCommRing J G O₂).obj)
          ((presheafRestrictedModules J G (O₂ := O₂)).obj N.val) :=
  rfl

omit [G.IsCocontinuous J K] [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
  [K.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- The presheaf of modules underlying the restriction of a sheaf of modules is the restriction
of the underlying presheaf of modules. -/
theorem presheafRestrictedModules_obj_val
    (N : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₂)) :
    (presheafRestrictedModules J G (O₂ := O₂)).obj N.val =
      ((restrictedModules J G (O₂ := O₂)).obj N).val :=
  rfl

omit [G.IsCocontinuous J K] [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
  [K.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- **The presheaf-level half of the comparison**: forget, tensor on the right with `N`, then
restrict along `G` is restrict, forget, then tensor on the right with the restriction of `N`.

Both sides are the same functor, and `rfl` nevertheless does not prove this: the three steps it
is assembled from are each a cheap `rfl` and their composite is not — see the implementation
notes of `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/DenseSubsiteSheafTensor.lean`, which is
the same assembly for a dense subsite inclusion and the other tensor spelling. -/
theorem forget_tensorRight_comp_presheafRestrictedModules
    (N : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₂)) :
    (SheafOfModules.forget.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₂) ⋙
        _root_.AlgebraicGeometry.SheafOfModules.PresheafOfModules.tensorRight (O := O₂.obj) N.val) ⋙
        presheafRestrictedModules J G (O₂ := O₂) =
      (restrictedModules J G (O₂ := O₂) ⋙
          SheafOfModules.forget.{u}
            (Stacks.SheafOfModules.Tensor.ringSheaf (restrictedCommRing J G O₂))) ⋙
        _root_.AlgebraicGeometry.SheafOfModules.PresheafOfModules.tensorRight
          (O := (restrictedCommRing J G O₂).obj)
          ((restrictedModules J G (O₂ := O₂)).obj N).val := by
  rw [← presheafRestrictedModules_obj_val, ← forget_comp_presheafRestrictedModules]
  exact congrArg
    (fun F => SheafOfModules.forget.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₂) ⋙ F)
    (tensorRight_comp_presheafRestrictedModules J G N)

omit [G.IsCocontinuous J K] [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- `AlgebraicGeometry.SheafOfModules.sheafTensorRight` on the target site, unfolded into its
three factors and reassociated so that the sheafification factor stands next to the
restriction. -/
theorem sheafTensorRight_comp_restrictedModules
    (N : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₂)) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor O₂).flip.obj N) ⋙
        restrictedModules J G (O₂ := O₂) =
      (SheafOfModules.forget.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₂) ⋙
        _root_.AlgebraicGeometry.SheafOfModules.PresheafOfModules.tensorRight (O := O₂.obj) N.val) ⋙
        (PresheafOfModules.sheafification.{u} (R := Stacks.SheafOfModules.Tensor.ringSheaf O₂)
            (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O₂).obj) ⋙
          restrictedModules J G (O₂ := O₂)) :=
  rfl

omit [G.IsCocontinuous J K] [K.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- `AlgebraicGeometry.SheafOfModules.sheafTensorRight` on the source site, precomposed with the
restriction and unfolded into its three factors. -/
theorem restrictedModules_comp_sheafTensorRight
    (N : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₂)) :
    ((restrictedModules J G (O₂ := O₂) ⋙
          SheafOfModules.forget.{u}
            (Stacks.SheafOfModules.Tensor.ringSheaf (restrictedCommRing J G O₂))) ⋙
        _root_.AlgebraicGeometry.SheafOfModules.PresheafOfModules.tensorRight
          (O := (restrictedCommRing J G O₂).obj)
          ((restrictedModules J G (O₂ := O₂)).obj N).val) ⋙
      PresheafOfModules.sheafification.{u}
        (R := Stacks.SheafOfModules.Tensor.ringSheaf (restrictedCommRing J G O₂))
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf (restrictedCommRing J G O₂)).obj) =
      restrictedModules J G (O₂ := O₂) ⋙
        ((Stacks.SheafOfModules.Tensor.sheafTensor (restrictedCommRing J G O₂)).flip.obj
          ((restrictedModules J G (O₂ := O₂)).obj N)) :=
  rfl

omit [G.IsCocontinuous J K] [K.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- The right-hand crossing of the comparison, assembled from
`Stacks.Sheaves.Differentials.forget_tensorRight_comp_presheafRestrictedModules` and
`restrictedModules_comp_sheafTensorRight`. -/
theorem forget_tensorRight_comp_presheafRestrictedModules_sheafification
    (N : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₂)) :
    (SheafOfModules.forget.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₂) ⋙
        _root_.AlgebraicGeometry.SheafOfModules.PresheafOfModules.tensorRight (O := O₂.obj) N.val) ⋙
        (presheafRestrictedModules J G (O₂ := O₂) ⋙
          PresheafOfModules.sheafification.{u}
            (R := Stacks.SheafOfModules.Tensor.ringSheaf (restrictedCommRing J G O₂))
            (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf (restrictedCommRing J G O₂)).obj)) =
      restrictedModules J G (O₂ := O₂) ⋙
        ((Stacks.SheafOfModules.Tensor.sheafTensor (restrictedCommRing J G O₂)).flip.obj
          ((restrictedModules J G (O₂ := O₂)).obj N)) :=
  (congrArg (fun F => F ⋙ PresheafOfModules.sheafification.{u}
      (R := Stacks.SheafOfModules.Tensor.ringSheaf (restrictedCommRing J G O₂))
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf (restrictedCommRing J G O₂)).obj))
    (forget_tensorRight_comp_presheafRestrictedModules J G N)).trans
    (restrictedModules_comp_sheafTensorRight J G N)

/-- **Restriction along `G` commutes with the tensor product of sheaves of modules**:
`G^{-1}(M ⊗_{O₂} N) ≅ G^{-1}M ⊗_{G^{-1}O₂} G^{-1}N`, naturally in `M`, for the tensor product
`Stacks.SheafOfModules.Tensor.sheafTensor`. -/
def restrictedSheafTensorRightIso
    (N : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₂)) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor O₂).flip.obj N) ⋙
        restrictedModules J G (O₂ := O₂) ≅
      restrictedModules J G (O₂ := O₂) ⋙
        ((Stacks.SheafOfModules.Tensor.sheafTensor (restrictedCommRing J G O₂)).flip.obj
          ((restrictedModules J G (O₂ := O₂)).obj N)) :=
  eqToIso (sheafTensorRight_comp_restrictedModules J G N) ≪≫
    Functor.isoWhiskerLeft
      (SheafOfModules.forget.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₂) ⋙
        _root_.AlgebraicGeometry.SheafOfModules.PresheafOfModules.tensorRight (O := O₂.obj) N.val)
      (Stacks.SheafOfModules.PushforwardSheafification.pushforwardSheafifyNatIso.{u} J G
        (Stacks.SheafOfModules.Tensor.ringSheaf O₂)).symm ≪≫
    eqToIso (forget_tensorRight_comp_presheafRestrictedModules_sheafification J G N)

end Tensor

end Stacks.Sheaves.Differentials

end
