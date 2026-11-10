module

public import Mathlib.CategoryTheory.Sites.Equivalence
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackModuleNatIso
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackModulesOfIsoStructureMap
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardExact
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullbackUnitValue
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposHomComp
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullbackModulesComp
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposTwoMorphismModules
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposInverseImageExact
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposRingImageComposition
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureMapSharp
public import StacksFrontier.CategoryTheory.Adjunction.Mates
public import StacksFrontier.CategoryTheory.Sites.Modules.Localization.InverseImageComparison
public import StacksFrontier.CategoryTheory.Sites.Modules.Localization.RingedToposRelocalizedMorphism
public import StacksFrontier.CategoryTheory.Sites.Simplicial.ComponentSheafify
public import StacksFrontier.CategoryTheory.Sites.Simplicial.RingedMorphism
public import StacksFrontier.CategoryTheory.Sites.Simplicial.TotalAugmentationComponents
public import StacksFrontier.CategoryTheory.Sites.Simplicial.TotalMorphismBaseChange
public import StacksFrontier.Deformation.ToposThickening.Trivialization.RingedToposComp
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite
public import StacksFrontier.CategoryTheory.Adjunction.MateOfUnitSquare
public import StacksFrontier.CategoryTheory.Adjunction.MatesChangeOfCategories
public import StacksFrontier.CategoryTheory.Sites.Simplicial.TotalMorphismBeckChevalley

/-!
# The morphisms of ringed topoi induced by a morphism of ringed simplicial sites

A morphism between ringed simplicial sites in the sense of
`CategoryTheory.CocontinuousSimplicialSite.RingedMorphism` induces a morphism of the total
ringed topoi and, in every simplicial degree, a morphism of the component ringed topoi of
Stacks 0D72. The resulting square of ringed topoi commutes over the square of topoi of the
unringed case, and on sheaves of modules the inverse image to a component of a direct image
along the total morphism is the degreewise direct image of the inverse image to that component.

## Main definitions

* `CategoryTheory.CocontinuousSimplicialSite.Morphism.componentInverseImageCommRingIso`: the
  comparison of the two inverse images of sheaves of commutative rings around the square of
  simplicial degree `n`, which is the identification `gₙ⁻¹h_{total}⁻¹𝒪' = hₙ⁻¹𝒪'ₙ` the source
  uses to define the degreewise structure map.
* `CategoryTheory.CocontinuousSimplicialSite.RingedMorphism.totalRingedToposHom`: the induced
  morphism of total ringed topoi.
* `CategoryTheory.CocontinuousSimplicialSite.RingedMorphism.componentRingedToposHom`: the
  induced morphism of component ringed topoi in a given simplicial degree.
* `AlgebraicGeometry.RingedToposHom.pullbackUnderlyingIsoOfIsIso`: for a morphism of ringed
  topoi with invertible structure map, the underlying sheaf of sets of the pullback of a sheaf
  of modules is the inverse image of the underlying sheaf.
* `CategoryTheory.SimplicialSiteSituation.componentPullbackUnderlyingIso`: that comparison at
  the canonical morphism from a simplicial component, whose structure map is invertible. This
  is the identification `gₙ^*ℱ = gₙ⁻¹ℱ` on which the source's last assertion rests.
* `CategoryTheory.CocontinuousSimplicialSite.Morphism.totalPushforwardRestrictRingMap` and
  `.totalPushforwardRestrictModulesIso`: the mixed comparison of Stacks 0D96 at the level of
  sheaves of rings and at the level of sheaves of modules.
* `CategoryTheory.CocontinuousSimplicialSite.RingedMorphism.componentRingedToposHom_twoIso`: the
  degreewise square read as a 2-isomorphism of morphisms of ringed topoi in the sense of
  Stacks 04IC, which is how the source's equality of morphisms of ringed topoi acts on sheaves
  of modules.
* `CategoryTheory.CocontinuousSimplicialSite.RingedMorphism.componentPushforwardModulesComparison`:
  the canonical comparison `(g'ₙ)^* ∘ h_{total,*} ⟶ h_{n,*} ∘ gₙ^*` of the source's last
  assertion, the mate of that square on direct images of sheaves of modules.

## Main results

* `CategoryTheory.CocontinuousSimplicialSite.Morphism.componentInverseImageIso_conjugate`
  identifies the comparison of inverse images with the conjugate of the comparison of direct
  images of the unringed case, so it is not an arbitrary isomorphism.
* `CategoryTheory.CocontinuousSimplicialSite.RingedMorphism.componentRingedToposHom_commutes`:
  the square of ringed topoi formed by the total morphism, the degreewise morphism and the two
  component morphisms commutes.
* `CategoryTheory.SimplicialSiteSituation.componentPullbackUnderlyingIso_unit` pins that
  comparison down: it is inverse to the unit of extension of scalars, hence is the canonical
  comparison of Stacks 03D2 and not an arbitrary isomorphism.
* `CategoryTheory.CocontinuousSimplicialSite.RingedMorphism.componentPushforwardModulesForgetIso`:
  the source's last assertion, on underlying sheaves of sets. Inverse image to the component of
  degree `n` of a direct image of sheaves of modules along the total morphism is the degreewise
  direct image of the inverse image to that component.
* `CategoryTheory.CocontinuousSimplicialSite.RingedMorphism.componentPushforwardModulesSquareIso`
  and `.componentPullbackModulesSquareIso`: the degreewise square on direct images and on
  pullbacks of sheaves of modules. These are the source's commuting diagrams of ringed topoi
  read on sheaves of modules, and they are unconditional.
* In `CategoryTheory.CocontinuousSimplicialSite.RingedMorphism`,
  `componentPushforwardModulesComparison_mate`: the comparison of the last assertion is pinned
  by that square — its mate is the square.
* In `CategoryTheory.CocontinuousSimplicialSite.RingedMorphism`,
  `isIso_componentPushforwardModulesComparison` and `componentPushforwardModulesIso`: the source's
  last assertion on sheaves of modules — the canonical comparison
  `(g'ₙ)^* ∘ h_{total,*} ⟶ h_{n,*} ∘ gₙ^*` is invertible.
* `AlgebraicGeometry.RingedToposHom.pullbackAdjPushforwardModules_unit_app_underlying` and
  `AlgebraicGeometry.RingedToposHom.isIso_mateEquiv_symm_pushforwardModules_of_isIso`: for
  morphisms of ringed topoi with invertible structure maps, the unit of `f^* ⊣ f_*` is the unit
  of the underlying topoi, and the mate of a square of direct images of sheaves of modules is
  invertible as soon as the mate of the underlying square of sheaves of sets is.

## Implementation notes

The homomorphism of structure sheaves of a `RingedMorphism` is stored at the level of sheaves of
*rings*, which is the level at which Stacks 0DGZ states it, while a ringed topos in this
development — `AlgebraicGeometry.RingedTopos`, after Stacks 01D3 part (1) — carries a sheaf of
*commutative* rings. So the statements below quantify over a `RingedMorphism` whose two sheaves
of rings are the underlying sheaves of rings of given sheaves of commutative rings, which is
exactly the generality in which "morphism of ringed topoi" exists here; the passage from the one
level to the other costs nothing, since `sheafCompose J (forget₂ CommRingCat RingCat)` is fully
faithful (`Stacks.Sheaves.ToposPullback.fullyFaithfulForgetCommRingSheaf`) and the inverse image
of the underlying sheaf of rings *is* the underlying sheaf of rings of the inverse image, on the
nose. `CategoryTheory.CocontinuousSimplicialSite.RingedMorphism.commRingHom` is that passage and
`.commRingHom_forget` records that it changes nothing.

The structure map of the induced morphism of total ringed topoi is stored in direct-image form
`𝒪' ⟶ h_{total,*}𝒪`, matching the field of `AlgebraicGeometry.RingedToposHom`; it is the adjunct
of `commRingHom` under `Stacks.Sheaves.ToposPushforward.commRingImageAdjunction`, and
`totalRingedToposHom_fSharpInverseImage` says the two forms carry the same information, as
Stacks 0DGZ asserts.

The source writes an equality of morphisms of ringed topoi around each degreewise square. Since
composition of the associated sheaf functors is only canonical up to isomorphism, the square is
expressed by an isomorphism of the two inverse images of sheaves of commutative rings together
with the compatibility of the two composite structure maps. The isomorphism is obtained from the
comparison of direct images of the unringed case by conjugation along the two adjunctions, and
then transported to sheaves of commutative rings; the transport is unique with the given
underlying map of sheaves of sets, by
`Stacks.Sheaves.ToposPushforward.inverseImageCommRingIsoOfToposIso_existsUnique`.

The degreewise structure map is the inverse image to the component of the total structure map,
read through the two identifications of the source: the comparison just described turns
`hₙ⁻¹𝒪'ₙ` into `gₙ⁻¹h_{total}⁻¹𝒪'`, and the comparison of Stacks 0D72 turns `gₙ⁻¹𝒪` into `𝒪ₙ`.
With that definition the commutativity of the square is a cancellation of the comparisons
against their inverses, which is also how the source argues.

This file treats the cocontinuous case. The continuous case (A) of Stacks 09WE is
`StacksFrontier/CategoryTheory/Sites/Simplicial/RingedToposMorphismContinuous.lean`.

### The assertion on sheaves of modules

The source's last assertion is the identity `(g'ₙ)^* ∘ h_{total,*} = h_{n,*} ∘ gₙ^*` of functors
`Mod(𝒪) ⟶ Mod(𝒪'ₙ)`, and its proof has two ingredients: that `gₙ^*` and `(g'ₙ)^*` are inverse
image on modules, and the unringed identity of Stacks 0D96. Both are carried out, the second at
the level of sheaves of modules and not merely of sheaves of sets.

The first: the structure sheaf of a component is by construction a restriction of the total one,
so the component structure map is invertible
(`CategoryTheory.SimplicialSiteSituation.isIso_componentRingedToposHom_fSharpInverseImage`) and
the pullback of modules along the component inclusion performs no genuine extension of scalars.
`AlgebraicGeometry.RingedToposHom.pullbackUnderlyingIsoOfIsIso` records that for any morphism of
ringed topoi with invertible structure map, by way of the unit of the change-of-rings adjunction
of Stacks 03CZ, which is invertible there because extension of scalars along an isomorphism is
an equivalence; `componentPullbackUnderlyingIso` is its instance at a component, and
`componentPullbackUnderlyingIso_unit` says the comparison is inverse to that unit, which is what
makes it the canonical one.

The second: `CocontinuousSimplicialSite.Morphism.totalPushforwardRestrictModulesIso` lifts the
mixed comparison `ν := totalPushforwardRestrictIso` of Stacks 0D96 to sheaves of modules. For a
sheaf of rings `R` on the total site of the source it exhibits the transport of a sheaf of
`R`-modules along `h_{total,*}` followed by `(g'ₙ)⁻¹` as isomorphic to its transport along
`gₙ⁻¹` followed by `h_{n,*}`, the comparison being `ν` itself and the scalars being read through
the corresponding comparison `totalPushforwardRestrictRingMap` of the two transported sheaves of
rings. This is a genuine module-level statement: `ν` is additive and linear for the two
transported module structures, not merely a comparison of underlying sheaves of sets. The
ring-level case for sheaves of *commutative* rings is `totalPushforwardRestrictCommRingIso`, and
`RingedMorphism.componentPushforwardModulesForgetIso` is the version of the source's identity,
for the actual structure sheaves, on underlying sheaves of sets.

The two ingredients are joined through the mate. The degreewise diagram is read as the source
writes it, as an equality of morphisms of ringed topoi; Stacks 04IC reads such an equality as a
2-isomorphism of the two composites `h_{total} ∘ gₙ` and `g'ₙ ∘ h_n`, and
`componentRingedToposHom_twoIso` is that 2-isomorphism: the comparison of the direct images is
the one of Stacks 0D96, and the compatibility with the three structure maps is
`componentRingedToposHom_commutes` transposed from the inverse-image to the direct-image form,
which is formal adjunction calculus and is
`AlgebraicGeometry.RingedToposHom.TwoIso.ofInverseImageIso`.

A 2-isomorphism of morphisms of ringed topoi acts on sheaves of modules, so this gives the
source's commuting diagrams on sheaves of modules, on direct images as
`componentPushforwardModulesSquareIso` and — by uniqueness of left adjoints — on pullbacks as
`componentPullbackModulesSquareIso`. Neither is a statement about underlying sheaves of sets:
the comparisons are additive and linear.

The source's last assertion is the invertibility of the *mate* of the square of direct images
under the two adjunctions `gₙ^* ⊣ g_{n,*}` and `(g'ₙ)^* ⊣ (g'ₙ)_*` of Stacks 03D7. That mate is
`componentPushforwardModulesComparison`, pinned by `componentPushforwardModulesComparison_mate`.
Its invertibility is reduced to sheaves of sets: the two component morphisms have invertible
structure maps, so their pullbacks of modules are inverse images on underlying sheaves of sets
and their units are the units of the topoi
(`AlgebraicGeometry.RingedToposHom.pullbackAdjPushforwardModules_unit_app_underlying`); the mate
on sheaves of modules then lies over the mate of the square of topoi
(`Stacks.CategoryTheory.map_mateEquiv_symm_app_of_lift`), which is invertible by the
Beck–Chevalley property of the square of component inclusions,
`CategoryTheory.CocontinuousSimplicialSite.Morphism.isIso_totalComponentPushforwardMate`. The
latter is where the Guitart exactness of that square enters; the mate of an isomorphism is in
general only a morphism.

## References

* [Stacks Project, Tag 0DH0](https://stacks.math.columbia.edu/tag/0DH0)
* [Stacks Project, Tag 0DGZ](https://stacks.math.columbia.edu/tag/0DGZ)
* [Stacks Project, Tag 0D96](https://stacks.math.columbia.edu/tag/0D96)
* [Stacks Project, Tag 0D95](https://stacks.math.columbia.edu/tag/0D95)
* [Stacks Project, Tag 0D72](https://stacks.math.columbia.edu/tag/0D72)
* [Stacks Project, Tag 09WE](https://stacks.math.columbia.edu/tag/09WE)
* [Stacks Project, Tag 04IC](https://stacks.math.columbia.edu/tag/04IC)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
* [Stacks Project, Tag 03D2](https://stacks.math.columbia.edu/tag/03D2)
* [Stacks Project, Tag 01D3](https://stacks.math.columbia.edu/tag/01D3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward
open Stacks.Sheaves.RingedToposModules (extendScalarsFSharp inverseImageModules
  extendRestrictScalarsAdjunction fSharpCommRing
  inverseImageModuleSheafIso
  moduleSheafFunctor_map_inverseImageAdjDirectImageModules_unit_app'
  moduleSheafFunctor_map_inverseImageAdjDirectImageModules_homEquiv)
open Stacks.Sheaves.RingedToposModules.RingedToposHom
  (extendScalarsFSharpIsoRestrictScalarsOfIsIso)

universe u

namespace CategoryTheory

/-- Three nested pairs of mutually inverse morphisms cancel. -/
private theorem comp_cancel₃ {D : Type*} [Category D] {W X Y Z T : D}
    (a : W ⟶ X) (a' : X ⟶ W) (b : X ⟶ Y) (b' : Y ⟶ X) (c : Y ⟶ Z) (c' : Z ⟶ Y)
    (hc : c ≫ c' = 𝟙 Y) (hb : b ≫ b' = 𝟙 X) (ha : a ≫ a' = 𝟙 W) (k : W ⟶ T) :
    a ≫ b ≫ c ≫ c' ≫ b' ≫ a' ≫ k = k := by
  rw [← Category.assoc c c', hc, Category.id_comp, ← Category.assoc b b', hb,
    Category.id_comp, ← Category.assoc a a', ha, Category.id_comp]

/-! ### Components of the operations on 2-squares

The pasting of 2-squares below is read componentwise.  Mathlib's whiskering and associator
lemmas do not apply to a pasting of `CategoryTheory.TwoSquare`s, whose functor arguments are not
determined by matching against the type `TwoSquare T L R B`, so the components are recorded
here.
-/

section TwoSquares

variable {D₁ D₂ D₃ D₄ D₇ D₈ : Type*} [Category* D₁] [Category* D₂] [Category* D₃]
  [Category* D₄] [Category* D₇] [Category* D₈]
  {T : D₁ ⥤ D₂} {L : D₁ ⥤ D₃} {R : D₂ ⥤ D₄} {Bo : D₃ ⥤ D₄}

/-- The component of the 2-square attached to a natural transformation. -/
private theorem twoSquare_mk_app (α : T ⋙ R ⟶ L ⋙ Bo) (c : D₁) :
    (TwoSquare.mk T L R Bo α).app c = α.app c := rfl

/-- The component of a vertical composition of 2-squares. -/
private theorem twoSquare_vComp_app {L' : D₃ ⥤ D₇} {R'' : D₄ ⥤ D₈} {B'' : D₇ ⥤ D₈}
    (w : TwoSquare T L R Bo) (w' : TwoSquare Bo L' R'' B'') (c : D₁) :
    (TwoSquare.vComp w w').app c =
      R''.map (w.app c) ≫ w'.app (L.obj c) := by
  simp [TwoSquare.vComp]

/-- The component of a 2-square whiskered on the left. -/
private theorem twoSquare_whiskerLeft_app {L' : D₁ ⥤ D₃} (w : TwoSquare T L R Bo) (α : L ⟶ L')
    (c : D₁) :
    (TwoSquare.whiskerLeft w α).app c = w.app c ≫ Bo.map (α.app c) := rfl

/-- The component of a 2-square whiskered on the right. -/
private theorem twoSquare_whiskerRight_app {R' : D₂ ⥤ D₄} (w : TwoSquare T L R' Bo)
    (α : R ⟶ R') (c : D₁) :
    (TwoSquare.whiskerRight w α).app c = α.app (T.obj c) ≫ w.app c := rfl

/-- Whiskering a 2-square on the right by an identity changes nothing. -/
private theorem twoSquare_whiskerRight_id (w : TwoSquare T L R Bo) :
    TwoSquare.whiskerRight w (𝟙 R) = w :=
  NatTrans.ext (funext fun c => by simp)

/-- Whiskering a 2-square on the left by an identity changes nothing. -/
private theorem twoSquare_whiskerLeft_id (w : TwoSquare T L R Bo) :
    TwoSquare.whiskerLeft w (𝟙 L) = w :=
  NatTrans.ext (funext fun c => by simp)

end TwoSquares

end CategoryTheory

namespace AlgebraicGeometry.RingedToposHom

variable {X : RingedTopos.{u, u, u}} {Y : RingedTopos.{u, u, u}} {Z : RingedTopos.{u, u, u}}

/-- The inverse-image form of the structure map of a composite of morphisms of ringed topoi is
the inverse image along the inner morphism of the structure map of the outer one, followed by the
structure map of the inner one. -/
theorem comp_fSharpInverseImage (g : RingedToposHom Y Z) (f : RingedToposHom X Y) :
    (g.comp f).fSharpInverseImage = compFSharpInverseImage g f :=
  X.forgetRing.map_injective
    ((comp_fSharpInverseImage_forget g f).trans
      (forget_map_compFSharpInverseImage g f).symm)

section PushforwardUnderlying

variable [X.J.HasSheafCompose (forget RingCat.{u})]
  [Y.J.HasSheafCompose (forget RingCat.{u})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  (f : RingedToposHom X Y)

/-- The comparison of the underlying sheaf of sets of a direct image of sheaves of modules with
the direct image of the underlying sheaf of sets is the identity. -/
private theorem pushforwardModulesUnderlyingIso_hom_eq_id :
    (pushforwardModulesUnderlyingIso f).hom =
      𝟙 (f.pushforwardModules ⋙ Sheaf.moduleSheafFunctor
        ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O))) :=
  rfl

/-- The same comparison read in the other direction. -/
private theorem pushforwardModulesUnderlyingIso_inv_eq_id :
    (pushforwardModulesUnderlyingIso f).inv =
      𝟙 (f.pushforwardModules ⋙ Sheaf.moduleSheafFunctor
        ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O))) :=
  rfl

variable [Z.J.HasSheafCompose (forget RingCat.{u})]
  [Z.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]

/-- On underlying sheaves of sets the compositor of direct images of sheaves of modules is the
identity. -/
private theorem moduleSheafFunctor_map_pushforwardModulesCompIso_hom_app
    (g : RingedToposHom Y Z)
    (M : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O))) :
    (Sheaf.moduleSheafFunctor ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Z.J) Z.O))).map
        ((pushforwardModulesCompIso f g).hom.app M) =
      𝟙 (g.toToposHom.pushforward.obj (f.toToposHom.pushforward.obj
        (Sheaf.moduleSheaf ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O)) M))) :=
  rfl

/-- The same for the inverse compositor. -/
private theorem moduleSheafFunctor_map_pushforwardModulesCompIso_inv_app
    (g : RingedToposHom Y Z)
    (M : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O))) :
    (Sheaf.moduleSheafFunctor ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Z.J) Z.O))).map
        ((pushforwardModulesCompIso f g).inv.app M) =
      𝟙 (g.toToposHom.pushforward.obj (f.toToposHom.pushforward.obj
        (Sheaf.moduleSheaf ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O)) M))) :=
  rfl

end PushforwardUnderlying

/-! ### The pullback of modules along a morphism with invertible structure map

For a morphism of ringed topoi whose structure map `f♯ : f⁻¹O_D ⟶ O_C` is invertible, the
pullback of sheaves of modules performs no genuine extension of scalars, so its underlying
sheaf of sets is the inverse image of the underlying sheaf. That is the situation of the
canonical morphism from a simplicial component to the total ringed topos, whose structure
sheaf is by construction a restriction of the total one. -/

section InvertibleStructureMap

variable [X.J.HasSheafCompose (forget RingCat.{u})]
  [Y.J.HasSheafCompose (forget RingCat.{u})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  (f : RingedToposHom X Y) [IsIso f.fSharpInverseImage]

/-- Restriction of scalars along the inverse of an invertible structure map is an equivalence
of the categories of sheaves of modules. -/
theorem restrictScalars_fSharpInverseImage_inv_isEquivalence :
    Functor.IsEquivalence
      (SheafOfModules.restrictScalars.{u} (asIso f.toModulesHom.fSharpInverseImage).inv) :=
  (Stacks.Sheaves.RingedPoint.restrictScalarsEquivalenceOfIso
    (asIso f.toModulesHom.fSharpInverseImage)).isEquivalence_functor

variable [HasWeakSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- Extension of scalars along an invertible structure map is full, being isomorphic to
restriction of scalars along the inverse, which is an equivalence. -/
theorem extendScalarsFSharp_full : (extendScalarsFSharp f.toModulesHom).Full :=
  let _ := restrictScalars_fSharpInverseImage_inv_isEquivalence f
  Functor.Full.of_iso (extendScalarsFSharpIsoRestrictScalarsOfIsIso f.toModulesHom).symm

/-- Extension of scalars along an invertible structure map is faithful, for the same reason. -/
theorem extendScalarsFSharp_faithful : (extendScalarsFSharp f.toModulesHom).Faithful :=
  let _ := restrictScalars_fSharpInverseImage_inv_isEquivalence f
  Functor.Faithful.of_iso (extendScalarsFSharpIsoRestrictScalarsOfIsIso f.toModulesHom).symm

/-- The change-of-rings adjunction of Stacks 03CZ along the structure map of a morphism of
ringed topoi: extension of scalars along `f♯` is left adjoint to restriction of scalars along
it. This is the second factor of the pullback of sheaves of modules. It is the canonical
adjunction `extendRestrictScalarsFSharpAdjunction` read at `f.toModulesHom`. -/
abbrev fSharpAdjunction := f.toModulesHom.extendRestrictScalarsFSharpAdjunction

/-- When the structure map is invertible, the unit of the change-of-rings adjunction along it
is a natural isomorphism, its left adjoint being fully faithful. -/
instance isIso_fSharpAdjunction_unit : IsIso (fSharpAdjunction f).unit :=
  @Adjunction.unit_isIso_of_L_fully_faithful _ _ _ _ _ _ (fSharpAdjunction f)
    (extendScalarsFSharp_full f) (extendScalarsFSharp_faithful f)

variable [X.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{u})]

/-- The unit of the change-of-rings adjunction along an invertible structure map, whiskered
onto the inverse image of sheaves of modules and read on underlying sheaves of sets: an
isomorphism from the underlying sheaf of the inverse image of a module to the underlying sheaf
of its pullback. -/
def pullbackUnitUnderlyingIso :
    inverseImageModules f.toToposHom ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O) ⋙
        Sheaf.moduleSheafFunctor
          (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ≅
      f.toModulesHom.pullbackModules ⋙ Sheaf.moduleSheafFunctor
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O) :=
  Functor.isoWhiskerLeft
    (inverseImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
    (Functor.isoWhiskerRight (asIso (fSharpAdjunction f).unit)
      (Sheaf.moduleSheafFunctor
        (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))))

/-- The whiskered unit is, in each component, the underlying map of the unit itself. -/
theorem pullbackUnitUnderlyingIso_hom_app
    (M : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O)) :
    (pullbackUnitUnderlyingIso f).hom.app M =
      (Sheaf.moduleSheafFunctor
          (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).map
        ((fSharpAdjunction f).unit.app
          ((inverseImageModules f.toToposHom
            ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O)).obj M)) :=
  rfl

/-- **The pullback of sheaves of modules along a morphism of ringed topoi with invertible
structure map has the inverse image as its underlying sheaf**, naturally in the module. The
pullback is the inverse image of Stacks 03D2 followed by extension of scalars along `f♯`; an
invertible `f♯` makes the unit of the change-of-rings adjunction an isomorphism, and
restriction of scalars leaves the underlying sheaf unchanged. -/
@[sga "4 IV 13.2.3" "Exceptional clause"]
def pullbackUnderlyingIsoOfIsIso :
    f.toModulesHom.pullbackModules ⋙
        Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ≅
      Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ⋙
        f.toToposHom.inverseImage :=
  (pullbackUnitUnderlyingIso f).symm ≪≫
    inverseImageModuleSheafIso f.toToposHom
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O)

/-- The comparison `pullbackUnderlyingIsoOfIsIso` is the canonical one: it is inverse to the
unit of extension of scalars, so precomposing it with that unit returns the comparison of
Stacks 03D2 identifying the underlying sheaf of the inverse image of modules with the inverse
image of the underlying sheaf. -/
theorem pullbackUnderlyingIsoOfIsIso_unit
    (M : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O)) :
    (Sheaf.moduleSheafFunctor
          (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).map
        ((fSharpAdjunction f).unit.app
          ((inverseImageModules f.toToposHom
            ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O)).obj M)) ≫
      (pullbackUnderlyingIsoOfIsIso f).hom.app M =
    (inverseImageModuleSheafIso f.toToposHom
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O)).hom.app M :=
  (pullbackUnitUnderlyingIso f).hom_inv_id_app_assoc M _

/-- The same identity at the level of natural isomorphisms: the unit comparison followed by
`pullbackUnderlyingIsoOfIsIso` is the comparison of Stacks 03D2. -/
theorem pullbackUnitUnderlyingIso_trans :
    pullbackUnitUnderlyingIso f ≪≫ pullbackUnderlyingIsoOfIsIso f =
      inverseImageModuleSheafIso f.toToposHom
        ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O) :=
  (pullbackUnitUnderlyingIso f).self_symm_id_assoc _

/-- **The comparison of the underlying sheaf of a pullback of modules with the inverse image is
the mate of the comparison for direct images.** For a morphism of ringed topoi with invertible
structure map, the mate of `pullbackUnderlyingIsoOfIsIso` under the adjunction of Stacks 03D7 and
the adjunction of the underlying morphism of topoi is
`AlgebraicGeometry.RingedToposHom.pushforwardModulesUnderlyingIso`, which is the identity.

Both sides are determined by the square of the two units, so the proof is
`CategoryTheory.mateEquiv_eq_of_unit`: the unit of Stacks 03D7 splits by the unit of a composite
adjunction transported along an isomorphism into the unit of Stacks 03D3 and the unit of
extension of scalars, the first becomes the unit of the morphism of topoi by
`moduleSheafFunctor_map_inverseImageAdjDirectImageModules_unit_app'` (in the namespace
`Stacks.Sheaves.RingedToposModules`), the second is `pullbackUnderlyingIsoOfIsIso` itself by
`AlgebraicGeometry.RingedToposHom.pullbackUnitUnderlyingIso_hom_app`, and the transport along
`toModulesPushforwardIso` is the identity on underlying sheaves. -/
theorem mateEquiv_pullbackUnderlyingIsoOfIsIso_inv :
    mateEquiv (pullbackAdjPushforwardModules f) f.toToposHom.adj
        (TwoSquare.mk _ _ _ _ (pullbackUnderlyingIsoOfIsIso f).inv) =
      TwoSquare.mk _ _ _ _ (pushforwardModulesUnderlyingIso f).hom :=
  mateEquiv_eq_of_unit _ _ _ _ fun M => by
    have hgen : ∀ {CC : Type _} [Category CC] {DD : Type _} [Category DD] {EE : Type _}
        [Category EE] {F : CC ⥤ DD} {G : DD ⥤ CC} {F' : DD ⥤ EE} {G' : EE ⥤ DD} {K : EE ⥤ CC}
        (adj₁ : F ⊣ G) (adj₂ : F' ⊣ G') (iso : G' ⋙ G ≅ K) (X : CC),
        ((adj₁.comp adj₂).ofNatIsoRight iso).unit.app X =
          adj₁.unit.app X ≫ G.map (adj₂.unit.app (F.obj X)) ≫ iso.hom.app (F'.obj (F.obj X)) := by
      intros; simp [Adjunction.comp_unit_app]
    have h0 := hgen
      (Stacks.Sheaves.RingedToposModules.inverseImageAdjDirectImageModules
        f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) (fSharpAdjunction f)
      f.toModulesPushforwardIso M
    have h1 := moduleSheafFunctor_map_inverseImageAdjDirectImageModules_unit_app'
      f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) M
    have h2 := Stacks.Sheaves.RingedToposModules.moduleSheafFunctor_map_directImageModules_map
      f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
      ((fSharpAdjunction f).unit.app
        ((inverseImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj M))
    have h4 : (pullbackUnderlyingIsoOfIsIso f).inv.app M =
        (Sheaf.moduleSheafFunctor (inverseImageRingSheaf f.toToposHom
            (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).map
          ((fSharpAdjunction f).unit.app
            ((inverseImageModules f.toToposHom
              (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj M)) :=
      Category.id_comp _
    change f.toToposHom.adj.unit.app
      (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) M) ≫
          f.toToposHom.pushforward.map ((pullbackUnderlyingIsoOfIsIso f).inv.app M) =
        (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map
          ((((Stacks.Sheaves.RingedToposModules.inverseImageAdjDirectImageModules f.toToposHom
                (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).comp
                  (fSharpAdjunction f)).ofNatIsoRight
              f.toModulesPushforwardIso).unit.app M) ≫ 𝟙 _
    rw [h0, h4, Functor.map_comp, Functor.map_comp, h1, h2]
    change _ = (_ ≫ _ ≫ 𝟙 _) ≫ 𝟙 _
    rw [Category.comp_id]
    exact congrArg (f.toToposHom.adj.unit.app
      (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) M) ≫ ·)
      (Category.comp_id _).symm

/-- **The unit of `f^* ⊣ f_*` on underlying sheaves of sets, for an invertible structure map.**
Read on underlying sheaves of sets and followed by the identification
`pullbackUnderlyingIsoOfIsIso` of `f^*M` with `f⁻¹M`, the unit of the adjunction of Stacks 03D7
on sheaves of modules is the unit of the adjunction `f⁻¹ ⊣ f_*` of the underlying topoi. -/
theorem pullbackAdjPushforwardModules_unit_app_underlying
    (M : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O)) :
    (Sheaf.moduleSheafFunctor ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O)).map
        ((pullbackAdjPushforwardModules f).unit.app M) ≫
      f.toToposHom.pushforward.map ((pullbackUnderlyingIsoOfIsIso f).hom.app M) =
    f.toToposHom.adj.unit.app
      (Sheaf.moduleSheaf ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O) M) := by
  have e1 : (pullbackAdjPushforwardModules f).unit.app M =
      (Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules f.toModulesHom).homEquiv
          M _ (𝟙 _) ≫ f.toModulesPushforwardIso.hom.app _ := by
    rw [← Adjunction.homEquiv_id]
    exact Adjunction.homEquiv_ofNatIsoRight_apply _ _ _
  have e2 :
      (Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules f.toModulesHom).homEquiv
        M _ (𝟙 _) =
      (Stacks.Sheaves.RingedToposModules.inverseImageAdjDirectImageModules f.toToposHom
          (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).homEquiv _ _
        ((fSharpAdjunction f).homEquiv _ _ (𝟙 _)) :=
    DFunLike.congr_fun (congrFun (congrFun (Adjunction.comp_homEquiv _ _) _) _) _
  have e3 :=
    moduleSheafFunctor_map_inverseImageAdjDirectImageModules_homEquiv
    f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ((fSharpAdjunction f).homEquiv
      ((inverseImageModules f.toToposHom
        ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O)).obj M) _ (𝟙 _))
  have e4 : (Sheaf.moduleSheafFunctor ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O)).map
      (f.toModulesPushforwardIso.hom.app (f.toModulesHom.pullbackModules.obj M)) =
      𝟙 (f.toToposHom.pushforward.obj (Sheaf.moduleSheaf
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
        (f.toModulesHom.pullbackModules.obj M))) :=
    Stacks.Sheaves.RingedToposModules.moduleSheafFunctor_map_ofSheafHom _ _ _
  have e5 := pullbackUnderlyingIsoOfIsIso_unit f M
  have e6 : (fSharpAdjunction f).homEquiv
      ((inverseImageModules f.toToposHom
        ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O)).obj M) _ (𝟙 _) =
      (fSharpAdjunction f).unit.app _ := Adjunction.homEquiv_id _ _
  have e7 : (inverseImageModuleSheafIso f.toToposHom
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O)).hom.app M = 𝟙 _ := rfl
  refine ((congrArg (fun t => t ≫ f.toToposHom.pushforward.map
    ((pullbackUnderlyingIsoOfIsIso f).hom.app M)) ((congrArg _ e1).trans
      (Functor.map_comp _ _ _))).trans ?_)
  refine ((congrArg (fun t => (_ ≫ t) ≫ f.toToposHom.pushforward.map
    ((pullbackUnderlyingIsoOfIsIso f).hom.app M)) e4).trans ?_)
  refine ((congrArg (fun t => (t ≫ 𝟙 _) ≫ f.toToposHom.pushforward.map
    ((pullbackUnderlyingIsoOfIsIso f).hom.app M)) ((congrArg _ e2).trans e3)).trans ?_)
  refine (congrArg (fun t => t ≫ f.toToposHom.pushforward.map
    ((pullbackUnderlyingIsoOfIsIso f).hom.app M))
      ((Category.comp_id _).trans (Adjunction.homEquiv_unit _ _ _ _))).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (fun t => f.toToposHom.adj.unit.app _ ≫ t)
    (CategoryTheory.Functor.map_comp f.toToposHom.pushforward _ _).symm).trans ?_
  have e5' : (Sheaf.moduleSheafFunctor (inverseImageRingSheaf f.toToposHom
      (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).map ((fSharpAdjunction f).homEquiv
        ((inverseImageModules f.toToposHom
          ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O)).obj M) _ (𝟙 _)) ≫
      (pullbackUnderlyingIsoOfIsIso f).hom.app M =
        𝟙 (f.toToposHom.inverseImage.obj
          (((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O).moduleSheaf M)) := by
    rw [e6]
    exact e5.trans e7
  refine (congrArg (fun t => f.toToposHom.adj.unit.app _ ≫ f.toToposHom.pushforward.map t)
    e5').trans ?_
  rw [CategoryTheory.Functor.map_id]
  exact Category.comp_id _

/-- The unit of `f^* ⊣ f_*` on underlying sheaves of sets, with the identity comparison of the
direct image inserted. -/
private theorem unit_app_underlying_comp (X : SheafOfModules.{u}
    ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O)) :
    (Sheaf.moduleSheafFunctor ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O)).map
      ((pullbackAdjPushforwardModules f).unit.app X) ≫
      (pushforwardModulesUnderlyingIso f).hom.app (f.toModulesHom.pullbackModules.obj X) ≫
      f.toToposHom.pushforward.map ((pullbackUnderlyingIsoOfIsIso f).hom.app X) =
      f.toToposHom.adj.unit.app
        ((Sheaf.moduleSheafFunctor
          ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O)).obj X) :=
  (whisker_eq _ (Category.id_comp _)).trans
    (pullbackAdjPushforwardModules_unit_app_underlying f X)

end InvertibleStructureMap

/-! ### The mate of a square of direct images of sheaves of modules

A 2-isomorphism of ringed topoi `l ∘ g ≅ g' ∘ k` gives a square of direct images of sheaves of
modules, and, through the adjunctions `g^* ⊣ g_*` and `g'^* ⊣ g'_*`, a mate
`l_* ⋙ g'^* ⟶ g^* ⋙ k_*`. When the structure maps of `g` and `g'` are invertible, the two
pullbacks are inverse images on underlying sheaves of sets, and the mate lies over the mate of
the square of underlying direct images; so it is invertible as soon as that mate is. -/

section SquareMate

variable {A B A' B' : RingedTopos.{u, u, u}}
  [A.J.HasSheafCompose (forget RingCat.{u})] [B.J.HasSheafCompose (forget RingCat.{u})]
  [A'.J.HasSheafCompose (forget RingCat.{u})] [B'.J.HasSheafCompose (forget RingCat.{u})]
  [A.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [B.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [A'.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [B'.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [A.J.HasSheafCompose (forget AddCommGrpCat.{u})] [B.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [A'.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [B'.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [HasWeakSheafify A.J AddCommGrpCat.{u}] [A.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify A'.J AddCommGrpCat.{u}] [A'.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  (g : RingedToposHom A B) (g' : RingedToposHom A' B') (k : RingedToposHom A A')
  (l : RingedToposHom B B') [IsIso g.fSharpInverseImage] [IsIso g'.fSharpInverseImage]
  (t : TwoIso.{u, u, u, u, u, u} (l.comp g) (g'.comp k))

/-- **The mate of a square of direct images of sheaves of modules is invertible if the mate of
the underlying square of sheaves of sets is**, for a 2-isomorphism `l ∘ g ≅ g' ∘ k` of morphisms
of ringed topoi in which `g` and `g'` have invertible structure maps. -/
theorem isIso_mateEquiv_symm_pushforwardModules_of_isIso
    [IsIso ((mateEquiv g.toToposHom.adj g'.toToposHom.adj).symm
      (TwoSquare.mk _ _ _ _ t.e.hom))] :
    IsIso ((mateEquiv (pullbackAdjPushforwardModules g) (pullbackAdjPushforwardModules g')).symm
      (TwoSquare.mk _ _ _ _ ((pushforwardModulesCompIso g l).symm ≪≫ t.pushforwardModulesIso ≪≫
        pushforwardModulesCompIso k g').hom)) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro M
  have hβ : ∀ Y, (Sheaf.moduleSheafFunctor
    ((Stacks.SheafOfModules.Tensor.ringSheaf (J := B'.J)) B'.O)).map
      (((pushforwardModulesCompIso g l).symm ≪≫ t.pushforwardModulesIso ≪≫
        pushforwardModulesCompIso k g').hom.app Y) ≫
      (pushforwardModulesUnderlyingIso g').hom.app (k.pushforwardModules.obj Y) ≫
      g'.toToposHom.pushforward.map ((pushforwardModulesUnderlyingIso k).hom.app Y) =
      (pushforwardModulesUnderlyingIso l).hom.app (g.pushforwardModules.obj Y) ≫
      l.toToposHom.pushforward.map ((pushforwardModulesUnderlyingIso g).hom.app Y) ≫
      t.e.hom.app ((Sheaf.moduleSheafFunctor
        ((Stacks.SheafOfModules.Tensor.ringSheaf (J := A.J)) A.O)).obj Y) := by
    intro Y
    refine (whisker_eq _ ((Category.id_comp _).trans
      (g'.toToposHom.pushforward.map_id _))).trans ((Category.comp_id _).trans ?_)
    refine Eq.trans ?_ ((Category.id_comp _).trans ((eq_whisker
      (l.toToposHom.pushforward.map_id _) _).trans (Category.id_comp _))).symm
    rfl
  have key := Stacks.CategoryTheory.map_mateEquiv_symm_app_of_lift
    (pullbackAdjPushforwardModules g) (pullbackAdjPushforwardModules g')
    g.toToposHom.adj g'.toToposHom.adj
    (TwoSquare.mk _ _ _ _ ((pushforwardModulesCompIso g l).symm ≪≫ t.pushforwardModulesIso ≪≫
        pushforwardModulesCompIso k g').hom) (TwoSquare.mk _ _ _ _ t.e.hom)
    (pushforwardModulesUnderlyingIso g) (pushforwardModulesUnderlyingIso g')
    (pushforwardModulesUnderlyingIso l) (pushforwardModulesUnderlyingIso k)
    (pullbackUnderlyingIsoOfIsIso g) (pullbackUnderlyingIsoOfIsIso g')
    (unit_app_underlying_comp g) (unit_app_underlying_comp g') hβ M
  have := NatIso.isIso_app_of_isIso ((mateEquiv g.toToposHom.adj g'.toToposHom.adj).symm
    (TwoSquare.mk _ _ _ _ t.e.hom))
    ((Sheaf.moduleSheafFunctor ((Stacks.SheafOfModules.Tensor.ringSheaf (J := B.J)) B.O)).obj M)
  have := IsIso.of_isIso_fac_right key
  exact isIso_of_reflects_iso _
    (Sheaf.moduleSheafFunctor ((Stacks.SheafOfModules.Tensor.ringSheaf (J := A'.J)) A'.O))

end SquareMate

end AlgebraicGeometry.RingedToposHom

namespace CategoryTheory

/-! ### Sheafification of abelian sheaves on a simplicial component

The pullback of sheaves of modules asks its source site to have sheafification of abelian
sheaves, and to have the maps inverted by it be exactly the locally bijective ones. Both hold on
a simplicial component, which is a small category at the site universe. They are activated
`local`ly so that no new `HasWeakSheafify` instance is exported; the first of them is
`CategoryTheory.SimplicialSiteSituation.hasWeakSheafifyComponent`. -/

attribute [local instance] SimplicialSiteSituation.hasWeakSheafifyComponent

/-- On the degree-`n` simplicial component at the site universe, the maps inverted by
sheafification of abelian sheaves are exactly the locally bijective ones. -/
local instance wEqualsLocallyBijectiveComponent (S : SimplicialSiteSituation.{u})
    (n : SimplexCategory) :
    (S.componentTopology n).WEqualsLocallyBijective AddCommGrpCat.{u} :=
  letI : HasSheafify ((equivSmallModel.{u} (S.component n : Type u)).inverse.inducedTopology
      (S.componentTopology n)) AddCommGrpCat.{u} :=
    GrothendieckTopology.hasSheafify_addCommGrpCat.{u, u, u} _
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{u, u, u, u + 1, u}
    (S.componentTopology n)

namespace SimplicialSiteSituation

/-- The structure sheaf of the total ringed topos is the given sheaf of commutative rings. -/
@[simp] theorem totalRingedTopos_O (S : SimplicialSiteSituation.{u})
    (O : Sheaf S.totalTopology CommRingCat.{u}) : (S.totalRingedTopos O).O = O :=
  rfl

/-- The structure map of the canonical morphism from a simplicial component to the total ringed
topos is, in inverse-image form, the comparison of structure sheaves of Stacks 0D72. -/
@[stacks 0D72 "the structure map of the component morphism, in inverse-image form"]
theorem componentRingedToposHom_fSharpInverseImage (S : SimplicialSiteSituation.{u})
    (O : Sheaf S.totalTopology CommRingCat.{u}) (n : SimplexCategory) :
    (componentRingedToposHom S O n).fSharpInverseImage =
      (componentRingedTopos_restrictionIso S n).hom.app O :=
  ((commRingImageAdjunction (componentMorphism S n)).homEquiv O
    ((componentRingedTopos S O n).O)).symm_apply_apply _

/-- The structure map of the canonical morphism from a simplicial component is invertible: it
is the comparison of structure sheaves of Stacks 0D72, which is an isomorphism because the
component structure sheaf is literal restriction of the total one. -/
instance isIso_componentRingedToposHom_fSharpInverseImage (S : SimplicialSiteSituation.{u})
    (O : Sheaf S.totalTopology CommRingCat.{u}) (n : SimplexCategory) :
    IsIso (componentRingedToposHom S O n).fSharpInverseImage := by
  rw [componentRingedToposHom_fSharpInverseImage]
  exact (Iso.app (componentRingedTopos_restrictionIso S n) O).isIso_hom

section ComponentModules

variable (S : SimplicialSiteSituation.{u}) (O : Sheaf S.totalTopology CommRingCat.{u})
  (n : SimplexCategory)

/-- **Stacks 0DH0.** Restriction of sheaves of modules to the simplicial component of degree
`n` has the inverse image of sheaves of sets as its underlying sheaf, naturally in the module:
the component structure sheaf is itself the restriction of the total structure sheaf, so the
pullback of modules extends scalars along an isomorphism. -/
@[stacks 0DH0 "restriction of modules to components"]
def componentPullbackUnderlyingIso :
    (componentRingedToposHom S O n).toModulesHom.pullbackModules ⋙
        Sheaf.moduleSheafFunctor
          ((Stacks.SheafOfModules.Tensor.ringSheaf (J := (componentRingedTopos S O n).J))
          (componentRingedTopos S O n).O) ≅
      Sheaf.moduleSheafFunctor
        ((Stacks.SheafOfModules.Tensor.ringSheaf (J := (totalRingedTopos S O).J))
          (totalRingedTopos S O).O) ⋙
        (componentRingedToposHom S O n).toToposHom.inverseImage :=
  RingedToposHom.pullbackUnderlyingIsoOfIsIso.{u} (componentRingedToposHom S O n)

/-- **Stacks 0DH0.** The comparison of the previous declaration is the canonical one, not an
arbitrary isomorphism: precomposing it with the unit of extension of scalars along the
component structure map — which is what
`AlgebraicGeometry.RingedToposHom.pullbackUnitUnderlyingIso` is, by
`AlgebraicGeometry.RingedToposHom.pullbackUnitUnderlyingIso_hom_app` — returns the comparison
of Stacks 03D2 between the underlying sheaf of the inverse image of modules and the inverse
image of the underlying sheaf. -/
@[stacks 0DH0 "the canonical restriction of modules"]
theorem componentPullbackUnderlyingIso_unit :
    RingedToposHom.pullbackUnitUnderlyingIso (componentRingedToposHom S O n) ≪≫
        componentPullbackUnderlyingIso S O n =
      inverseImageModuleSheafIso (componentRingedToposHom S O n).toToposHom
        ((Stacks.SheafOfModules.Tensor.ringSheaf (J := (totalRingedTopos S O).J))
          (totalRingedTopos S O).O) :=
  RingedToposHom.pullbackUnitUnderlyingIso_trans (componentRingedToposHom S O n)

end ComponentModules

end SimplicialSiteSituation

namespace CocontinuousSimplicialSite

namespace Morphism

variable {C C' : CocontinuousSimplicialSite.{u}}

/-- The morphism of topoi from the component of simplicial degree `n` of the source to the total
topos of the target, through the total topos of the source. -/
abbrev viaTotalMorphism (h : Morphism C C') (n : SimplexCategory) :
    MorphismOfTopoi (Sheaf (C.situation.componentTopology n) (Type u))
      (Sheaf C'.situation.totalTopology (Type u)) :=
  h.totalMorphism.comp (SimplicialSiteSituation.componentMorphism C.situation n)

/-- The morphism of topoi from the component of simplicial degree `n` of the source to the total
topos of the target, through the component of simplicial degree `n` of the target. -/
abbrev viaComponentMorphism (h : Morphism C C') (n : SimplexCategory) :
    MorphismOfTopoi (Sheaf (C.situation.componentTopology n) (Type u))
      (Sheaf C'.situation.totalTopology (Type u)) :=
  (SimplicialSiteSituation.componentMorphism C'.situation n).comp
    ((SimplicialSiteMorphism.ofCocontinuous h).componentMorphism n)

/-- The comparison of the two inverse images of sheaves of sets around the square of simplicial
degree `n`, obtained by conjugating the comparison of direct images of Stacks 0D96 along the two
adjunctions. -/
def componentInverseImageIso (h : Morphism C C') (n : SimplexCategory) :
    (viaTotalMorphism h n).inverseImage ≅ (viaComponentMorphism h n).inverseImage :=
  (conjugateIsoEquiv (viaComponentMorphism h n).adj (viaTotalMorphism h n).adj).symm
    (h.totalComponentPushforwardIso n)

/-- The comparison of inverse images is the conjugate of the comparison of direct images of
Stacks 0D96, so it is not an arbitrary isomorphism of inverse images. -/
theorem componentInverseImageIso_conjugate (h : Morphism C C') (n : SimplexCategory) :
    conjugateIsoEquiv (viaComponentMorphism h n).adj (viaTotalMorphism h n).adj
        (componentInverseImageIso h n) =
      h.totalComponentPushforwardIso n :=
  Equiv.apply_symm_apply _ _

/-- **Stacks 0DH0.** The comparison of the two inverse images of sheaves of commutative rings
around the square of simplicial degree `n`. This is the identification
`gₙ⁻¹h_{total}⁻¹𝒪' = hₙ⁻¹(g'ₙ)⁻¹𝒪'` through which the source defines the degreewise structure
map. -/
@[stacks 0DH0 "the canonical ring comparison"]
def componentInverseImageCommRingIso (h : Morphism C C') (n : SimplexCategory) :
    inverseImageCommRingFunctor.{u, u, u, u, u, u} (viaTotalMorphism h n) ≅
      inverseImageCommRingFunctor.{u, u, u, u, u, u} (viaComponentMorphism h n) :=
  pullbackCommRingSheafFunctorIsoOfNatIso.{u, u, u, u, u, u}
    (C.situation.componentTopology n)
    (Φ := (viaTotalMorphism h n).inverseImage)
    (Φ' := (viaComponentMorphism h n).inverseImage) (componentInverseImageIso h n)

/-- **Stacks 0DH0.** The comparison of inverse images of sheaves of commutative rings has the
comparison of inverse images of sheaves of sets as its underlying map, which determines it
uniquely by
`Stacks.Sheaves.ToposPushforward.inverseImageCommRingIsoOfToposIso_existsUnique`. -/
@[stacks 0DH0 "the canonical underlying comparison"]
theorem componentInverseImageCommRingIso_forget (h : Morphism C C') (n : SimplexCategory)
    (O' : Sheaf C'.situation.totalTopology CommRingCat.{u}) :
    (sheafCompose (C.situation.componentTopology n) (forget CommRingCat.{u})).map
        ((componentInverseImageCommRingIso h n).hom.app O') =
      (componentInverseImageIso h n).hom.app
        ((sheafCompose C'.situation.totalTopology (forget CommRingCat.{u})).obj O') :=
  rfl

/-- The ring-level form of the comparison of Stacks 0D96: inverse image to the component of
simplicial degree `n`, applied to the direct image of sheaves of commutative rings along the
total morphism, is the degreewise direct image applied to inverse image to that component. -/
def totalPushforwardRestrictCommRingIso (h : Morphism C C') (n : SimplexCategory) :
    pushforwardCommRingFunctor.{u, u, u, u, u, u} h.totalMorphism ⋙
        inverseImageCommRingFunctor.{u, u, u, u, u, u}
          (SimplicialSiteSituation.componentMorphism C'.situation n) ≅
      inverseImageCommRingFunctor.{u, u, u, u, u, u}
          (SimplicialSiteSituation.componentMorphism C.situation n) ⋙
        pushforwardCommRingFunctor.{u, u, u, u, u, u}
          ((SimplicialSiteMorphism.ofCocontinuous h).componentMorphism n) :=
  pullbackCommRingSheafFunctorComp.{u, u, u, u, u, u, u} C'.situation.totalTopology
      (C'.situation.componentTopology n) h.totalMorphism.pushforward
      (SimplicialSiteSituation.componentMorphism C'.situation n).inverseImage ≪≫
    pullbackCommRingSheafFunctorIsoOfNatIso.{u, u, u, u, u, u}
      (C'.situation.componentTopology n)
      (Φ := h.totalMorphism.pushforward ⋙
        (SimplicialSiteSituation.componentMorphism C'.situation n).inverseImage)
      (Φ' := (SimplicialSiteSituation.componentMorphism C.situation n).inverseImage ⋙
        ((SimplicialSiteMorphism.ofCocontinuous h).componentMorphism n).pushforward)
      (h.totalPushforwardRestrictIso n) ≪≫
    (pullbackCommRingSheafFunctorComp.{u, u, u, u, u, u, u} (C.situation.componentTopology n)
      (C'.situation.componentTopology n)
      (SimplicialSiteSituation.componentMorphism C.situation n).inverseImage
      ((SimplicialSiteMorphism.ofCocontinuous h).componentMorphism n).pushforward).symm

/-! ### The mixed square of simplicial degree `n` on sheaves of modules

The comparison of Stacks 0D96 compares two functors of sheaves of sets from the total topos of
the source to the component topos of degree `n` of the target. Each of them transports the
module structure of a sheaf of modules on the total site, and the comparison carries the one
transported structure to the other: it is additive, and linear over the corresponding comparison
of the two transported sheaves of rings. -/

/-- Direct image along the total morphism followed by inverse image to the component of
simplicial degree `n`: the left-hand transporting functor of the mixed square of Stacks 0D96. -/
abbrev restrictTotalPushforward (h : Morphism C C') (n : SimplexCategory) :
    Sheaf C.situation.totalTopology (Type u) ⥤
      Sheaf (C'.situation.componentTopology n) (Type u) :=
  h.totalMorphism.pushforward ⋙
    (SimplicialSiteSituation.componentMorphism C'.situation n).inverseImage

/-- Inverse image to the component of simplicial degree `n` followed by the degreewise direct
image: the right-hand transporting functor of the mixed square of Stacks 0D96. -/
abbrev componentPushforwardRestrict (h : Morphism C C') (n : SimplexCategory) :
    Sheaf C.situation.totalTopology (Type u) ⥤
      Sheaf (C'.situation.componentTopology n) (Type u) :=
  (SimplicialSiteSituation.componentMorphism C.situation n).inverseImage ⋙
    ((SimplicialSiteMorphism.ofCocontinuous h).componentMorphism n).pushforward

/-- The comparison of Stacks 0D96 at the level of sheaves of rings: the transport of a sheaf of
rings on the total site along the two sides of the mixed square of simplicial degree `n` agree,
by a morphism whose underlying morphism of sheaves of sets is that comparison. -/
abbrev totalPushforwardRestrictRingMap (h : Morphism C C') (n : SimplexCategory)
    (R : Sheaf C.situation.totalTopology RingCat.{u}) :
    pullbackRingSheaf.{u, u, u, u, u, u} (C'.situation.componentTopology n)
        (restrictTotalPushforward h n) R ⟶
      pullbackRingSheaf.{u, u, u, u, u, u} (C'.situation.componentTopology n)
        (componentPushforwardRestrict h n) R :=
  pullbackRingSheafMapOfNatTrans.{u, u, u, u, u, u} (C'.situation.componentTopology n) R
    (h.totalPushforwardRestrictIso n).hom

/-- **The comparison of Stacks 0D96 on sheaves of modules.** Transporting a sheaf of modules on
the total site of the source along direct image to the target followed by inverse image to the
component of simplicial degree `n` gives the same sheaf of modules as transporting it along
inverse image to the component of that degree followed by the degreewise direct image — not
merely the same underlying sheaf of sets. The comparison is the one of Stacks 0D96 itself, and
the scalars are read through `totalPushforwardRestrictRingMap`.

This is the module-level lift of
`CategoryTheory.CocontinuousSimplicialSite.Morphism.totalPushforwardRestrictIso`: it says that
the comparison is additive and linear for the two transported module structures. -/
def totalPushforwardRestrictModulesIso (h : Morphism C C') (n : SimplexCategory)
    (R : Sheaf C.situation.totalTopology RingCat.{u}) :
    pullbackModuleFunctor.{u, u, u, u, u, u} (C'.situation.componentTopology n)
        (restrictTotalPushforward h n) R ≅
      pullbackModuleFunctor.{u, u, u, u, u, u} (C'.situation.componentTopology n)
          (componentPushforwardRestrict h n) R ⋙
        SheafOfModules.restrictScalars.{u} (totalPushforwardRestrictRingMap h n R) :=
  pullbackModuleFunctorIsoOfNatIso.{u, u, u, u, u, u} (C'.situation.componentTopology n) R
    (h.totalPushforwardRestrictIso n) (totalPushforwardRestrictRingMap h n R)
    (ringSheafMap_pullbackRingSheafMapOfNatTrans.{u, u, u, u, u, u}
      (C'.situation.componentTopology n) R (h.totalPushforwardRestrictIso n).hom)

variable {O : Sheaf C.situation.totalTopology CommRingCat.{u}}
  {O' : Sheaf C'.situation.totalTopology CommRingCat.{u}}

/-- The homomorphism of structure sheaves of a morphism between ringed simplicial sites whose
sheaves of rings are the underlying sheaves of rings of sheaves of *commutative* rings, read at
the commutative level: the inverse-image form `h_{total}⁻¹𝒪' ⟶ 𝒪`.

Forgetting commutativity is fully faithful on sheaves and the inverse image of the underlying
sheaf of rings is the underlying sheaf of rings of the inverse image on the nose, so nothing is
lost and nothing is chosen. -/
def commRingHom
    (h : Morphism C C') (φ : h.totalInverseImageRing
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := C'.situation.totalTopology) O')) ⟶
        (Stacks.SheafOfModules.Tensor.ringSheaf (J := C.situation.totalTopology) O)) :
    (inverseImageCommRingFunctor h.totalMorphism).obj O' ⟶ O :=
  (fullyFaithfulForgetCommRingSheaf C.situation.totalTopology).preimage
    (show (Stacks.forgetCommRingSheaf C.situation.totalTopology).obj
          ((inverseImageCommRingFunctor h.totalMorphism).obj O') ⟶
        (Stacks.forgetCommRingSheaf C.situation.totalTopology).obj O from φ)

/-- Reading the homomorphism of structure sheaves at the commutative level changes nothing: on
underlying sheaves of rings it is the given homomorphism. -/
theorem commRingHom_forget
    (h : Morphism C C') (φ : h.totalInverseImageRing
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := C'.situation.totalTopology) O')) ⟶
        (Stacks.SheafOfModules.Tensor.ringSheaf (J := C.situation.totalTopology) O)) :
    (Stacks.forgetCommRingSheaf C.situation.totalTopology).map (h.commRingHom φ) =
      (show (Stacks.forgetCommRingSheaf C.situation.totalTopology).obj
            ((inverseImageCommRingFunctor h.totalMorphism).obj O') ⟶
          (Stacks.forgetCommRingSheaf C.situation.totalTopology).obj O from φ) :=
  (fullyFaithfulForgetCommRingSheaf C.situation.totalTopology).map_preimage _

/-- **Stacks 0DH0.** The morphism of total ringed topoi induced by a morphism between ringed
simplicial sites. -/
@[stacks 0DH0 "the total morphism of ringed topoi"]
def totalRingedToposHom
    (h : Morphism C C') (φ : h.totalInverseImageRing
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := C'.situation.totalTopology) O')) ⟶
        (Stacks.SheafOfModules.Tensor.ringSheaf (J := C.situation.totalTopology) O)) :
    RingedToposHom (C.situation.totalRingedTopos O) (C'.situation.totalRingedTopos O') where
  toToposHom := h.totalMorphism
  fSharp := (commRingImageAdjunction h.totalMorphism).homEquiv O' O (h.commRingHom φ)

/-- The underlying geometric morphism of the total morphism of ringed topoi is the morphism of
total topoi of Stacks 0D96. -/
theorem totalRingedToposHom_toToposHom
    (h : Morphism C C') (φ : h.totalInverseImageRing
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := C'.situation.totalTopology) O')) ⟶
        (Stacks.SheafOfModules.Tensor.ringSheaf (J := C.situation.totalTopology) O)) :
    (h.totalRingedToposHom φ).toToposHom = h.totalMorphism :=
  rfl

/-- The structure map of the total morphism of ringed topoi is, in inverse-image form, the given
homomorphism of total structure sheaves. -/
theorem totalRingedToposHom_fSharpInverseImage
    (h : Morphism C C') (φ : h.totalInverseImageRing
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := C'.situation.totalTopology) O')) ⟶
        (Stacks.SheafOfModules.Tensor.ringSheaf (J := C.situation.totalTopology) O)) :
    (h.totalRingedToposHom φ).fSharpInverseImage = (h.commRingHom φ) :=
  ((commRingImageAdjunction h.totalMorphism).homEquiv O' O).symm_apply_apply _

/-- The structure map of the degreewise morphism of ringed topoi, in inverse-image form: the
inverse image to the component of the total structure map, read through the comparison of inverse
images around the degreewise square and the comparisons of structure sheaves of Stacks 0D72. -/
def componentFSharpInverseImage
    (h : Morphism C C') (φ : h.totalInverseImageRing
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := C'.situation.totalTopology) O')) ⟶
        (Stacks.SheafOfModules.Tensor.ringSheaf (J := C.situation.totalTopology) O))
    (n : SimplexCategory) :
    (inverseImageCommRingFunctor
        ((SimplicialSiteMorphism.ofCocontinuous h).componentMorphism n)).obj
          ((C'.situation.componentRingedTopos O' n).O) ⟶
      (C.situation.componentRingedTopos O n).O :=
  (inverseImageCommRingFunctor
      ((SimplicialSiteMorphism.ofCocontinuous h).componentMorphism n)).map
        ((SimplicialSiteSituation.componentRingedTopos_restrictionIso C'.situation n).inv.app O') ≫
    (inverseImageCommRingComp (SimplicialSiteSituation.componentMorphism C'.situation n)
      ((SimplicialSiteMorphism.ofCocontinuous h).componentMorphism n)).hom.app O' ≫
    (h.componentInverseImageCommRingIso n).inv.app O' ≫
    (inverseImageCommRingComp h.totalMorphism
      (SimplicialSiteSituation.componentMorphism C.situation n)).inv.app O' ≫
    (inverseImageCommRingFunctor
      (SimplicialSiteSituation.componentMorphism C.situation n)).map (h.commRingHom φ) ≫
    (SimplicialSiteSituation.componentRingedTopos_restrictionIso C.situation n).hom.app O

/-- **Stacks 0DH0.** The morphism of component ringed topoi in simplicial degree `n` induced by a
morphism between ringed simplicial sites. -/
@[stacks 0DH0 "the component morphisms of ringed topoi"]
def componentRingedToposHom
    (h : Morphism C C') (φ : h.totalInverseImageRing
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := C'.situation.totalTopology) O')) ⟶
        (Stacks.SheafOfModules.Tensor.ringSheaf (J := C.situation.totalTopology) O))
    (n : SimplexCategory) :
    RingedToposHom (C.situation.componentRingedTopos O n)
      (C'.situation.componentRingedTopos O' n) where
  toToposHom := (SimplicialSiteMorphism.ofCocontinuous h).componentMorphism n
  fSharp :=
    (commRingImageAdjunction
        ((SimplicialSiteMorphism.ofCocontinuous h).componentMorphism n)).homEquiv
      ((C'.situation.componentRingedTopos O' n).O)
      ((C.situation.componentRingedTopos O n).O)
      ((h.componentFSharpInverseImage φ) n)

/-- **Stacks 0DH0.** The underlying geometric morphism of the degreewise morphism of ringed
topoi is the component morphism of topoi of Stacks 0D95. -/
@[stacks 0DH0 "the underlying degreewise geometric morphisms"]
theorem componentRingedToposHom_toToposHom
    (h : Morphism C C') (φ : h.totalInverseImageRing
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := C'.situation.totalTopology) O')) ⟶
        (Stacks.SheafOfModules.Tensor.ringSheaf (J := C.situation.totalTopology) O))
    (n : SimplexCategory) :
    ((h.componentRingedToposHom φ) n).toToposHom =
      (SimplicialSiteMorphism.ofCocontinuous h).componentMorphism n :=
  rfl

/-- The structure map of the degreewise morphism of ringed topoi is the prescribed one. -/
theorem componentRingedToposHom_fSharpInverseImage
    (h : Morphism C C') (φ : h.totalInverseImageRing
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := C'.situation.totalTopology) O')) ⟶
        (Stacks.SheafOfModules.Tensor.ringSheaf (J := C.situation.totalTopology) O))
    (n : SimplexCategory) :
    ((h.componentRingedToposHom φ) n).fSharpInverseImage = (h.componentFSharpInverseImage φ) n :=
  Equiv.symm_apply_apply _ _

/-- **Stacks 0DH0.** The square of ringed topoi formed by the total morphism, the degreewise
morphism and the two canonical morphisms from the components of simplicial degree `n` commutes:
the comparison of inverse images identifies the two composite structure maps. -/
@[stacks 0DH0 "the commutative squares of ringed topoi"]
theorem componentRingedToposHom_commutes
    (h : Morphism C C') (φ : h.totalInverseImageRing
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := C'.situation.totalTopology) O')) ⟶
        (Stacks.SheafOfModules.Tensor.ringSheaf (J := C.situation.totalTopology) O))
    (n : SimplexCategory) :
    (h.componentInverseImageCommRingIso n).hom.app O' ≫
        ((C'.situation.componentRingedToposHom O' n).comp
          ((h.componentRingedToposHom φ) n)).fSharpInverseImage =
      ((h.totalRingedToposHom φ).comp
        (C.situation.componentRingedToposHom O n)).fSharpInverseImage := by
  have hc :
      (inverseImageCommRingFunctor
            ((SimplicialSiteMorphism.ofCocontinuous h).componentMorphism n)).map
          ((SimplicialSiteSituation.componentRingedTopos_restrictionIso
            C'.situation n).hom.app O') ≫
        (inverseImageCommRingFunctor
            ((SimplicialSiteMorphism.ofCocontinuous h).componentMorphism n)).map
          ((SimplicialSiteSituation.componentRingedTopos_restrictionIso
            C'.situation n).inv.app O') = 𝟙 _ := by
    rw [← Functor.map_comp, Iso.hom_inv_id_app, Functor.map_id]
  rw [RingedToposHom.comp_fSharpInverseImage, RingedToposHom.comp_fSharpInverseImage]
  simp only [RingedToposHom.compFSharpInverseImage,
    componentRingedToposHom_fSharpInverseImage,
    SimplicialSiteSituation.componentRingedToposHom_fSharpInverseImage,
    totalRingedToposHom_fSharpInverseImage, componentFSharpInverseImage,
    componentRingedToposHom_toToposHom, totalRingedToposHom_toToposHom,
    SimplicialSiteSituation.componentRingedToposHom_toToposHom,
    SimplicialSiteSituation.totalRingedTopos_O]
  exact comp_cancel₃ _ _ _ _ _ _ hc
    ((inverseImageCommRingComp (SimplicialSiteSituation.componentMorphism C'.situation n)
      ((SimplicialSiteMorphism.ofCocontinuous h).componentMorphism n)).inv_hom_id_app O')
    ((h.componentInverseImageCommRingIso n).hom_inv_id_app O') _

/-- **Stacks 0DH0, the assertion on sheaves of modules, on underlying sheaves of sets.**
Inverse image to the simplicial component of degree `n` of a direct image of sheaves of modules
along the total morphism is the degreewise direct image of the inverse image to that component.

The comparison is the one of Stacks 0D96 and nothing else: the pullback of modules along a
component inclusion is inverse image on underlying sheaves of sets, by
`CategoryTheory.SimplicialSiteSituation.componentPullbackUnderlyingIso`, and the direct image of
modules is direct image there on the nose. -/
@[stacks 0DH0 "the underlying restriction of the direct image of modules"]
def componentPushforwardModulesForgetIso
    (h : Morphism C C') (φ : h.totalInverseImageRing
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := C'.situation.totalTopology) O')) ⟶
        (Stacks.SheafOfModules.Tensor.ringSheaf (J := C.situation.totalTopology) O))
    (n : SimplexCategory) :
    (h.totalRingedToposHom φ).pushforwardModules ⋙
        (C'.situation.componentRingedToposHom O' n).toModulesHom.pullbackModules ⋙
          Sheaf.moduleSheafFunctor
            ((Stacks.SheafOfModules.Tensor.ringSheaf
              (J := (C'.situation.componentRingedTopos O' n).J)
              (C'.situation.componentRingedTopos O' n).O)) ≅
      (C.situation.componentRingedToposHom O n).toModulesHom.pullbackModules ⋙
        ((h.componentRingedToposHom φ) n).pushforwardModules ⋙
          Sheaf.moduleSheafFunctor
            ((Stacks.SheafOfModules.Tensor.ringSheaf
              (J := (C'.situation.componentRingedTopos O' n).J)
              (C'.situation.componentRingedTopos O' n).O)) :=
  Functor.isoWhiskerLeft (h.totalRingedToposHom φ).pushforwardModules
      (SimplicialSiteSituation.componentPullbackUnderlyingIso C'.situation O' n) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (h.totalRingedToposHom φ).pushforwardModulesUnderlyingIso
      (C'.situation.componentRingedToposHom O' n).toToposHom.inverseImage ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft
      (Sheaf.moduleSheafFunctor
        ((Stacks.SheafOfModules.Tensor.ringSheaf (J := (C.situation.totalRingedTopos O).J)
          (C.situation.totalRingedTopos O).O)))
      (h.totalPushforwardRestrictIso n) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (SimplicialSiteSituation.componentPullbackUnderlyingIso C.situation O n).symm
      ((h.componentRingedToposHom φ) n).toToposHom.pushforward ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (C.situation.componentRingedToposHom O n).toModulesHom.pullbackModules
      ((h.componentRingedToposHom φ) n).pushforwardModulesUnderlyingIso.symm

/-! ### The degreewise square as a square of ringed topoi, and sheaves of modules

The source writes the degreewise diagram as an equality of morphisms of ringed topoi. Stacks
04IC reads such an assertion as a 2-isomorphism of the two composites, and that is the form in
which a commuting square of ringed topoi acts on sheaves of modules: the two composite direct
images of sheaves of modules are isomorphic, and so are the two composite pullbacks. The
comparison of the source's last assertion is then the mate of the square of direct images. -/

/-- The composite `h_{total} ∘ g_n` of morphisms of ringed topoi: from the ringed topos of the
simplicial component of degree `n` of the source to the total ringed topos of the target. -/
noncomputable abbrev viaTotalRingedToposHom
    (h : Morphism C C') (φ : h.totalInverseImageRing
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := C'.situation.totalTopology) O')) ⟶
        (Stacks.SheafOfModules.Tensor.ringSheaf (J := C.situation.totalTopology) O))
    (n : SimplexCategory) :
    RingedToposHom (C.situation.componentRingedTopos O n)
      (C'.situation.totalRingedTopos O') :=
  RingedToposHom.comp (X := C.situation.componentRingedTopos O n)
    (Y := C.situation.totalRingedTopos O) (Z := C'.situation.totalRingedTopos O')
    (h.totalRingedToposHom φ) (C.situation.componentRingedToposHom O n)

/-- The composite `g'_n ∘ h_n` of morphisms of ringed topoi: the other side of the degreewise
square of Stacks 0DH0. -/
noncomputable abbrev viaComponentRingedToposHom
    (h : Morphism C C') (φ : h.totalInverseImageRing
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := C'.situation.totalTopology) O')) ⟶
        (Stacks.SheafOfModules.Tensor.ringSheaf (J := C.situation.totalTopology) O))
    (n : SimplexCategory) :
    RingedToposHom (C.situation.componentRingedTopos O n)
      (C'.situation.totalRingedTopos O') :=
  RingedToposHom.comp (X := C.situation.componentRingedTopos O n)
    (Y := C'.situation.componentRingedTopos O' n) (Z := C'.situation.totalRingedTopos O')
    (C'.situation.componentRingedToposHom O' n) ((h.componentRingedToposHom φ) n)

/-- **Stacks 0DH0.** The degreewise square commutes as a square of *ringed* topoi, in the sense
of Stacks 04IC: the two composites `h_{total} ∘ g_n` and `g'_n ∘ h_n` are 2-isomorphic.

The comparison of the direct images is the one of Stacks 0D96, and the compatibility with the
three structure maps is `componentRingedToposHom_commutes` read on underlying sheaves of sets,
through `AlgebraicGeometry.RingedToposHom.TwoIso.ofInverseImageIso`, which transposes a
compatibility of the inverse-image forms into one of the direct-image forms. The underlying
comparison of inverse images is pinned by
`CategoryTheory.CocontinuousSimplicialSite.Morphism.componentInverseImageCommRingIso_forget`,
so this 2-isomorphism is not an arbitrary one. -/
@[stacks 0DH0 "the degreewise square as a 2-isomorphism of ringed topoi"]
noncomputable def componentRingedToposHom_twoIso
    (h : Morphism C C') (φ : h.totalInverseImageRing
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := C'.situation.totalTopology) O')) ⟶
        (Stacks.SheafOfModules.Tensor.ringSheaf (J := C.situation.totalTopology) O))
    (n : SimplexCategory) :
    RingedToposHom.TwoIso.{u, u, u, u, u, u}
      (viaTotalRingedToposHom h φ n) (viaComponentRingedToposHom h φ n) :=
  (RingedToposHom.TwoIso.ofInverseImageIso
    (p := viaComponentRingedToposHom h φ n) (q := viaTotalRingedToposHom h φ n)
    (h.componentInverseImageIso n) (by
      have E2 : (C.situation.componentRingedTopos O n).forgetRing.map
            ((h.componentInverseImageCommRingIso n).hom.app O') =
          (h.componentInverseImageIso n).hom.app
            ((C'.situation.totalRingedTopos O').forgetRing.obj
              (C'.situation.totalRingedTopos O').O) :=
        Morphism.componentInverseImageCommRingIso_forget h n O'
      exact (congrArg (fun z ↦ z ≫ (C.situation.componentRingedTopos O n).forgetRing.map
          (viaComponentRingedToposHom h φ n).fSharpInverseImage) E2).symm.trans
        ((CategoryTheory.Functor.map_comp _ _ _).symm.trans
          (congrArg (C.situation.componentRingedTopos O n).forgetRing.map
            ((h.componentRingedToposHom_commutes φ) n))))).symm

/-- **Stacks 0DH0, the degreewise square on direct images of sheaves of modules.** Direct image
to the total ringed topos of the target, taken through the component of degree `n` of the
source, agrees with direct image taken through the component of degree `n` of the target:

`h_{total,*} ∘ g_{n,*} ≅ g'_{n,*} ∘ h_{n,*}` on `Mod(𝒪_n)`.

This is the commuting square of ringed topoi of
`componentRingedToposHom_twoIso` read on sheaves of modules, and it is a genuine module-level
statement: the comparison is additive and linear, not merely a comparison of underlying sheaves
of sets. -/
@[stacks 0DH0 "the commutative squares, on direct images of sheaves of modules"]
noncomputable def componentPushforwardModulesSquareIso
    (h : Morphism C C') (φ : h.totalInverseImageRing
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := C'.situation.totalTopology) O')) ⟶
        (Stacks.SheafOfModules.Tensor.ringSheaf (J := C.situation.totalTopology) O))
    (n : SimplexCategory) :
    (C.situation.componentRingedToposHom O n).pushforwardModules ⋙
        (h.totalRingedToposHom φ).pushforwardModules ≅
      ((h.componentRingedToposHom φ) n).pushforwardModules ⋙
        (C'.situation.componentRingedToposHom O' n).pushforwardModules :=
  (RingedToposHom.pushforwardModulesCompIso (C.situation.componentRingedToposHom O n)
      (h.totalRingedToposHom φ)).symm ≪≫
    (componentRingedToposHom_twoIso h φ n).pushforwardModulesIso ≪≫
    RingedToposHom.pushforwardModulesCompIso ((h.componentRingedToposHom φ) n)
      (C'.situation.componentRingedToposHom O' n)

/-- **Stacks 0DH0, the degreewise square on pullbacks of sheaves of modules.** The same square,
read on pullbacks:

`g_n^* ∘ h_{total}^* ≅ h_n^* ∘ (g'_n)^*` on `Mod(𝒪')`.

Both sides are left adjoint to the two sides of `componentPushforwardModulesSquareIso`, so this
is uniqueness of left adjoints applied to that isomorphism. -/
@[stacks 0DH0 "the commutative squares, on pullbacks of sheaves of modules"]
noncomputable def componentPullbackModulesSquareIso
    (h : Morphism C C') (φ : h.totalInverseImageRing
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := C'.situation.totalTopology) O')) ⟶
        (Stacks.SheafOfModules.Tensor.ringSheaf (J := C.situation.totalTopology) O))
    (n : SimplexCategory) :
    (h.totalRingedToposHom φ).toModulesHom.pullbackModules ⋙
        (C.situation.componentRingedToposHom O n).toModulesHom.pullbackModules ≅
      (C'.situation.componentRingedToposHom O' n).toModulesHom.pullbackModules ⋙
        ((h.componentRingedToposHom φ) n).toModulesHom.pullbackModules :=
  (RingedToposHom.pullbackModulesCompIso (C.situation.componentRingedToposHom O n)
      (h.totalRingedToposHom φ)).symm ≪≫
    (componentRingedToposHom_twoIso h φ n).pullbackModulesIso ≪≫
    RingedToposHom.pullbackModulesCompIso ((h.componentRingedToposHom φ) n)
      (C'.situation.componentRingedToposHom O' n)

/-- **Stacks 0DH0, the comparison of the last assertion.** The canonical morphism of functors
`Mod(𝒪) ⟶ Mod(𝒪'_n)`

`(g'_n)^* ∘ h_{total,*} ⟶ h_{n,*} ∘ g_n^*`

attached to the degreewise square: the mate of `componentPushforwardModulesSquareIso` under the
two adjunctions `g_n^* ⊣ g_{n,*}` and `(g'_n)^* ⊣ (g'_n)_*` of Stacks 03D7. The source's last
assertion is that this comparison is invertible, which is the Beck–Chevalley content of the
degreewise square; see the implementation notes of this file. -/
@[stacks 0DH0 "the comparison of the last assertion, on sheaves of modules"]
noncomputable def componentPushforwardModulesComparison
    (h : Morphism C C') (φ : h.totalInverseImageRing
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := C'.situation.totalTopology) O')) ⟶
        (Stacks.SheafOfModules.Tensor.ringSheaf (J := C.situation.totalTopology) O))
    (n : SimplexCategory) :
    (h.totalRingedToposHom φ).pushforwardModules ⋙
        (C'.situation.componentRingedToposHom O' n).toModulesHom.pullbackModules ⟶
      (C.situation.componentRingedToposHom O n).toModulesHom.pullbackModules ⋙
        ((h.componentRingedToposHom φ) n).pushforwardModules :=
  (mateEquiv
      (RingedToposHom.pullbackAdjPushforwardModules
        (C.situation.componentRingedToposHom O n))
      (RingedToposHom.pullbackAdjPushforwardModules
        (C'.situation.componentRingedToposHom O' n))).symm
    (TwoSquare.mk _ _ _ _ (componentPushforwardModulesSquareIso h φ n).hom)

/-- **Stacks 0DH0.** The comparison of the last assertion is pinned by the degreewise square:
its mate under the two adjunctions of Stacks 03D7 is the square of direct images of sheaves of
modules. In particular it is not an arbitrary natural transformation. -/
@[stacks 0DH0 "the comparison of the last assertion is the mate of the square"]
theorem componentPushforwardModulesComparison_mate
    (h : Morphism C C') (φ : h.totalInverseImageRing
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := C'.situation.totalTopology) O')) ⟶
        (Stacks.SheafOfModules.Tensor.ringSheaf (J := C.situation.totalTopology) O))
    (n : SimplexCategory) :
    mateEquiv
        (RingedToposHom.pullbackAdjPushforwardModules
          (C.situation.componentRingedToposHom O n))
        (RingedToposHom.pullbackAdjPushforwardModules
          (C'.situation.componentRingedToposHom O' n))
        (componentPushforwardModulesComparison h φ n) =
      TwoSquare.mk _ _ _ _ (componentPushforwardModulesSquareIso h φ n).hom :=
  Equiv.apply_symm_apply _ _

/-- **The 2-isomorphism of the degreewise square is the comparison of Stacks 0D96.** The
isomorphism of direct images underlying `componentRingedToposHom_twoIso` is the inverse of
`CategoryTheory.CocontinuousSimplicialSite.Morphism.totalComponentPushforwardIso`.

The 2-isomorphism is built by conjugating the comparison of inverse images along the two
adjunctions, and that comparison is by construction the conjugate of the comparison of direct
images (`Morphism.componentInverseImageIso_conjugate`); conjugation is an equivalence, so the
two cancel. -/
theorem componentRingedToposHom_twoIso_e
    (h : Morphism C C') (φ : h.totalInverseImageRing
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := C'.situation.totalTopology) O')) ⟶
        (Stacks.SheafOfModules.Tensor.ringSheaf (J := C.situation.totalTopology) O))
    (n : SimplexCategory) :
    (componentRingedToposHom_twoIso h φ n).e = (h.totalComponentPushforwardIso n).symm :=
  congrArg Iso.symm (Morphism.componentInverseImageIso_conjugate h n)

/-- **The cube identity transferring Beck--Chevalley for the degreewise square from sheaves of
sets to sheaves of modules.** The comparison of Stacks 0D96 of the two composite direct images
of sheaves of sets, pasted with the two comparisons
`AlgebraicGeometry.RingedToposHom.mateEquiv_pullbackUnderlyingIsoOfIsIso_inv` of the underlying
sheaf of a pullback of modules and with the two identifications of the underlying sheaf of a
direct image of modules, is the square `componentPushforwardModulesSquareIso` of direct images
of sheaves of modules.

Four of the six faces are identities: the two mates are the identity by
`AlgebraicGeometry.RingedToposHom.mateEquiv_pullbackUnderlyingIsoOfIsIso_inv`, and the two
vertical comparisons are `AlgebraicGeometry.RingedToposHom.pushforwardModulesUnderlyingIso`,
which is `Iso.refl`. What is left is that the module square has the comparison of Stacks 0D96 as
its underlying map of sheaves of sets, which is
`AlgebraicGeometry.RingedToposHom.TwoIso.moduleSheafFunctor_map_pushforwardModulesIso_hom_app`
together with `componentRingedToposHom_twoIso_e` and the vanishing of the two compositors on
underlying sheaves. -/
theorem componentPushforwardModulesCube
    (h : Morphism C C') (φ : h.totalInverseImageRing
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := C'.situation.totalTopology) O')) ⟶
        (Stacks.SheafOfModules.Tensor.ringSheaf (J := C.situation.totalTopology) O))
    (n : SimplexCategory) :
    ((TwoSquare.vComp (mateEquiv
            (RingedToposHom.pullbackAdjPushforwardModules
              (C.situation.componentRingedToposHom O n))
            (C.situation.componentRingedToposHom O n).toToposHom.adj
            (TwoSquare.mk _ _ _ _ (RingedToposHom.pullbackUnderlyingIsoOfIsIso
              (C.situation.componentRingedToposHom O n)).inv))
          (TwoSquare.mk _ _ _ _
            (h.totalComponentPushforwardIso n).inv)).whiskerRight
            (RingedToposHom.pushforwardModulesUnderlyingIso
              (h.totalRingedToposHom φ)).hom).whiskerLeft
          (RingedToposHom.pushforwardModulesUnderlyingIso
            ((h.componentRingedToposHom φ) n)).inv =
      TwoSquare.vComp
        (TwoSquare.mk _ _ _ _ (componentPushforwardModulesSquareIso h φ n).hom)
        (mateEquiv
          (RingedToposHom.pullbackAdjPushforwardModules
            (C'.situation.componentRingedToposHom O' n))
          (C'.situation.componentRingedToposHom O' n).toToposHom.adj
          (TwoSquare.mk _ _ _ _ (RingedToposHom.pullbackUnderlyingIsoOfIsIso
            (C'.situation.componentRingedToposHom O' n)).inv)) := by
  rw [RingedToposHom.mateEquiv_pullbackUnderlyingIsoOfIsIso_inv
      (C.situation.componentRingedToposHom O n),
    RingedToposHom.mateEquiv_pullbackUnderlyingIsoOfIsIso_inv
      (C'.situation.componentRingedToposHom O' n),
    RingedToposHom.pushforwardModulesUnderlyingIso_hom_eq_id
      (C.situation.componentRingedToposHom O n),
    RingedToposHom.pushforwardModulesUnderlyingIso_hom_eq_id (h.totalRingedToposHom φ),
    RingedToposHom.pushforwardModulesUnderlyingIso_hom_eq_id
      (C'.situation.componentRingedToposHom O' n),
    RingedToposHom.pushforwardModulesUnderlyingIso_inv_eq_id
      ((h.componentRingedToposHom φ) n)]
  refine ((twoSquare_whiskerLeft_id _).trans (twoSquare_whiskerRight_id _)).trans ?_
  refine NatTrans.ext (funext fun Z => ?_)
  refine (twoSquare_vComp_app _ _ Z).trans ?_
  simp only [twoSquare_vComp_app, twoSquare_mk_app, NatTrans.id_app, Functor.comp_obj]
  refine (congrArg (fun x => x ≫ _) (CategoryTheory.Functor.map_id _ _)).trans ?_
  refine (Category.id_comp _).trans ?_
  refine (twoSquare_mk_app _ _).trans ?_
  refine Eq.trans ?_ (Category.comp_id _).symm
  change _ = (Sheaf.moduleSheafFunctor
    ((Stacks.SheafOfModules.Tensor.ringSheaf (J := (C'.situation.totalRingedTopos O').J)
      (C'.situation.totalRingedTopos O').O))).map
    ((RingedToposHom.pushforwardModulesCompIso (C.situation.componentRingedToposHom O n)
        (h.totalRingedToposHom φ)).inv.app Z ≫
      ((componentRingedToposHom_twoIso h φ n).pushforwardModulesIso.hom.app Z ≫
        (RingedToposHom.pushforwardModulesCompIso ((h.componentRingedToposHom φ) n)
          (C'.situation.componentRingedToposHom O' n)).hom.app Z))
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp,
    RingedToposHom.moduleSheafFunctor_map_pushforwardModulesCompIso_inv_app
      (C.situation.componentRingedToposHom O n) (h.totalRingedToposHom φ) Z,
    RingedToposHom.moduleSheafFunctor_map_pushforwardModulesCompIso_hom_app
      ((h.componentRingedToposHom φ) n) (C'.situation.componentRingedToposHom O' n) Z,
    RingedToposHom.TwoIso.moduleSheafFunctor_map_pushforwardModulesIso_hom_app
      (componentRingedToposHom_twoIso h φ n) Z,
    componentRingedToposHom_twoIso_e h φ n, Iso.symm_hom]
  exact ((Category.id_comp _).trans (Category.comp_id _)).symm

/-- **Stacks 0DH0, the last assertion: the comparison of the degreewise square is invertible.**
This is the Beck--Chevalley statement for the degreewise square at the level of sheaves of
modules.

It is the set-level statement
`CategoryTheory.CocontinuousSimplicialSite.Morphism.isIso_totalComponentPushforward_mate`
transferred along the forgetful functor from sheaves of modules to sheaves of sets, by
`Stacks.CategoryTheory.isIso_mateEquiv_symm_of_reflectsIsomorphisms`: the cube identity is
`componentPushforwardModulesCube`, the four side comparisons are invertible — two of them are
identities — and the forgetful functor reflects isomorphisms, which is all that device needs at
the corner it is applied to. -/
instance isIso_componentPushforwardModulesComparison
    (h : Morphism C C') (φ : h.totalInverseImageRing
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := C'.situation.totalTopology) O')) ⟶
        (Stacks.SheafOfModules.Tensor.ringSheaf (J := C.situation.totalTopology) O))
    (n : SimplexCategory) :
    IsIso (componentPushforwardModulesComparison h φ n) := by
  have hback : IsIso ((mateEquiv
      (C.situation.componentRingedToposHom O n).toToposHom.adj
      (C'.situation.componentRingedToposHom O' n).toToposHom.adj).symm
      (TwoSquare.mk
        (C.situation.componentRingedToposHom O n).toToposHom.pushforward
        ((h.componentRingedToposHom φ) n).toToposHom.pushforward
        (h.totalRingedToposHom φ).toToposHom.pushforward
        (C'.situation.componentRingedToposHom O' n).toToposHom.pushforward
        (h.totalComponentPushforwardIso n).inv)) :=
    Morphism.isIso_totalComponentPushforward_mate h n
  exact Stacks.CategoryTheory.isIso_mateEquiv_symm_of_reflectsIsomorphisms
    (RingedToposHom.pullbackAdjPushforwardModules (C.situation.componentRingedToposHom O n))
    (RingedToposHom.pullbackAdjPushforwardModules (C'.situation.componentRingedToposHom O' n))
    (C.situation.componentRingedToposHom O n).toToposHom.adj
    (C'.situation.componentRingedToposHom O' n).toToposHom.adj
    (TwoSquare.mk _ _ _ _ (RingedToposHom.pullbackUnderlyingIsoOfIsIso
      (C.situation.componentRingedToposHom O n)).inv)
    (TwoSquare.mk _ _ _ _ (RingedToposHom.pullbackUnderlyingIsoOfIsIso
      (C'.situation.componentRingedToposHom O' n)).inv)
    (RingedToposHom.pushforwardModulesUnderlyingIso (h.totalRingedToposHom φ)).hom
    (RingedToposHom.pushforwardModulesUnderlyingIso ((h.componentRingedToposHom φ) n)).inv
    (TwoSquare.mk _ _ _ _ (componentPushforwardModulesSquareIso h φ n).hom)
    (TwoSquare.mk _ _ _ _ (h.totalComponentPushforwardIso n).inv)
    (componentPushforwardModulesCube h φ n)

/-- **Stacks 0DH0, the last assertion, on sheaves of modules.** Inverse image to the simplicial
component of degree `n` of a direct image of sheaves of modules along the total morphism is the
degreewise direct image of the inverse image to that component:

`(g'_n)^* ∘ h_{total,*} ≅ h_{n,*} ∘ g_n^*` as functors `Mod(𝒪) ⟶ Mod(𝒪'_n)`,

the isomorphism being the canonical comparison `componentPushforwardModulesComparison`
attached to the degreewise square. That comparison is invertible by
`isIso_componentPushforwardModulesComparison`, which is the Beck–Chevalley statement for the
square; so this is unconditional, as is the assertion on underlying sheaves of sets,
`componentPushforwardModulesForgetIso`. -/
@[stacks 0DH0 "the last assertion, on sheaves of modules"]
noncomputable def componentPushforwardModulesIso
    (h : Morphism C C') (φ : h.totalInverseImageRing
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := C'.situation.totalTopology) O')) ⟶
        (Stacks.SheafOfModules.Tensor.ringSheaf (J := C.situation.totalTopology) O))
    (n : SimplexCategory) :
    (h.totalRingedToposHom φ).pushforwardModules ⋙
        (C'.situation.componentRingedToposHom O' n).toModulesHom.pullbackModules ≅
      (C.situation.componentRingedToposHom O n).toModulesHom.pullbackModules ⋙
        ((h.componentRingedToposHom φ) n).pushforwardModules :=
  asIso (componentPushforwardModulesComparison h φ n)

end Morphism

namespace RingedMorphism

variable {C C' : CocontinuousSimplicialSite.{u}}
  {O : Sheaf C.situation.totalTopology CommRingCat.{u}}
  {O' : Sheaf C'.situation.totalTopology CommRingCat.{u}}

/-- The homomorphism of structure sheaves of a morphism between ringed simplicial sites whose
sheaves of rings are the underlying sheaves of rings of sheaves of *commutative* rings, read at
the commutative level: the inverse-image form `h_{total}⁻¹𝒪' ⟶ 𝒪`.

Forgetting commutativity is fully faithful on sheaves and the inverse image of the underlying
sheaf of rings is the underlying sheaf of rings of the inverse image on the nose, so nothing is
lost and nothing is chosen. -/
def commRingHom
    (h : RingedMorphism C C'
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := C.situation.totalTopology)) O)
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := C'.situation.totalTopology)) O')) :
    (inverseImageCommRingFunctor h.hom.totalMorphism).obj O' ⟶ O :=
  (fullyFaithfulForgetCommRingSheaf C.situation.totalTopology).preimage
    (show (Stacks.forgetCommRingSheaf C.situation.totalTopology).obj
          ((inverseImageCommRingFunctor h.hom.totalMorphism).obj O') ⟶
        (Stacks.forgetCommRingSheaf C.situation.totalTopology).obj O from h.ringHom)

/-- Reading the homomorphism of structure sheaves at the commutative level changes nothing: on
underlying sheaves of rings it is the given homomorphism. -/
theorem commRingHom_forget
    (h : RingedMorphism C C'
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := C.situation.totalTopology)) O)
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := C'.situation.totalTopology)) O')) :
    (Stacks.forgetCommRingSheaf C.situation.totalTopology).map h.commRingHom =
      (show (Stacks.forgetCommRingSheaf C.situation.totalTopology).obj
            ((inverseImageCommRingFunctor h.hom.totalMorphism).obj O') ⟶
          (Stacks.forgetCommRingSheaf C.situation.totalTopology).obj O from h.ringHom) :=
  (fullyFaithfulForgetCommRingSheaf C.situation.totalTopology).map_preimage _

/-- **Stacks 0DH0.** The morphism of total ringed topoi induced by a morphism between ringed
simplicial sites. -/
@[stacks 0DH0 "the total morphism of ringed topoi"]
def totalRingedToposHom
    (h : RingedMorphism C C'
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := C.situation.totalTopology)) O)
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := C'.situation.totalTopology)) O')) :
    RingedToposHom (C.situation.totalRingedTopos O) (C'.situation.totalRingedTopos O') where
  toToposHom := h.hom.totalMorphism
  fSharp := (commRingImageAdjunction h.hom.totalMorphism).homEquiv O' O h.commRingHom

/-- The underlying geometric morphism of the total morphism of ringed topoi is the morphism of
total topoi of Stacks 0D96. -/
theorem totalRingedToposHom_toToposHom
    (h : RingedMorphism C C'
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := C.situation.totalTopology)) O)
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := C'.situation.totalTopology)) O')) :
    h.totalRingedToposHom.toToposHom = h.hom.totalMorphism :=
  rfl

/-- The structure map of the total morphism of ringed topoi is, in inverse-image form, the given
homomorphism of total structure sheaves. -/
theorem totalRingedToposHom_fSharpInverseImage
    (h : RingedMorphism C C'
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := C.situation.totalTopology)) O)
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := C'.situation.totalTopology)) O')) :
    h.totalRingedToposHom.fSharpInverseImage = h.commRingHom :=
  ((commRingImageAdjunction h.hom.totalMorphism).homEquiv O' O).symm_apply_apply _

/-- The structure map of the degreewise morphism of ringed topoi, in inverse-image form: the
inverse image to the component of the total structure map, read through the comparison of inverse
images around the degreewise square and the comparisons of structure sheaves of Stacks 0D72. -/
def componentFSharpInverseImage
    (h : RingedMorphism C C'
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := C.situation.totalTopology)) O)
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := C'.situation.totalTopology)) O'))
    (n : SimplexCategory) :
    (inverseImageCommRingFunctor
        ((SimplicialSiteMorphism.ofCocontinuous h.hom).componentMorphism n)).obj
          ((C'.situation.componentRingedTopos O' n).O) ⟶
      (C.situation.componentRingedTopos O n).O :=
  (inverseImageCommRingFunctor
      ((SimplicialSiteMorphism.ofCocontinuous h.hom).componentMorphism n)).map
        ((SimplicialSiteSituation.componentRingedTopos_restrictionIso C'.situation n).inv.app O') ≫
    (inverseImageCommRingComp (SimplicialSiteSituation.componentMorphism C'.situation n)
      ((SimplicialSiteMorphism.ofCocontinuous h.hom).componentMorphism n)).hom.app O' ≫
    (h.hom.componentInverseImageCommRingIso n).inv.app O' ≫
    (inverseImageCommRingComp h.hom.totalMorphism
      (SimplicialSiteSituation.componentMorphism C.situation n)).inv.app O' ≫
    (inverseImageCommRingFunctor
      (SimplicialSiteSituation.componentMorphism C.situation n)).map h.commRingHom ≫
    (SimplicialSiteSituation.componentRingedTopos_restrictionIso C.situation n).hom.app O

/-- **Stacks 0DH0.** The morphism of component ringed topoi in simplicial degree `n` induced by a
morphism between ringed simplicial sites. -/
@[stacks 0DH0 "the component morphisms of ringed topoi"]
def componentRingedToposHom
    (h : RingedMorphism C C'
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := C.situation.totalTopology)) O)
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := C'.situation.totalTopology)) O'))
    (n : SimplexCategory) :
    RingedToposHom (C.situation.componentRingedTopos O n)
      (C'.situation.componentRingedTopos O' n) where
  toToposHom := (SimplicialSiteMorphism.ofCocontinuous h.hom).componentMorphism n
  fSharp :=
    (commRingImageAdjunction
        ((SimplicialSiteMorphism.ofCocontinuous h.hom).componentMorphism n)).homEquiv
      ((C'.situation.componentRingedTopos O' n).O)
      ((C.situation.componentRingedTopos O n).O)
      (h.componentFSharpInverseImage n)

/-- **Stacks 0DH0.** The underlying geometric morphism of the degreewise morphism of ringed
topoi is the component morphism of topoi of Stacks 0D95. -/
@[stacks 0DH0 "the underlying degreewise geometric morphisms"]
theorem componentRingedToposHom_toToposHom
    (h : RingedMorphism C C'
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := C.situation.totalTopology)) O)
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := C'.situation.totalTopology)) O'))
    (n : SimplexCategory) :
    (h.componentRingedToposHom n).toToposHom =
      (SimplicialSiteMorphism.ofCocontinuous h.hom).componentMorphism n :=
  rfl

/-- The structure map of the degreewise morphism of ringed topoi is the prescribed one. -/
theorem componentRingedToposHom_fSharpInverseImage
    (h : RingedMorphism C C'
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := C.situation.totalTopology)) O)
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := C'.situation.totalTopology)) O'))
    (n : SimplexCategory) :
    (h.componentRingedToposHom n).fSharpInverseImage = h.componentFSharpInverseImage n :=
  Equiv.symm_apply_apply _ _

/-- **Stacks 0DH0.** The square of ringed topoi formed by the total morphism, the degreewise
morphism and the two canonical morphisms from the components of simplicial degree `n` commutes:
the comparison of inverse images identifies the two composite structure maps. -/
@[stacks 0DH0 "the commutative squares of ringed topoi"]
theorem componentRingedToposHom_commutes
    (h : RingedMorphism C C'
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := C.situation.totalTopology)) O)
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := C'.situation.totalTopology)) O'))
    (n : SimplexCategory) :
    (h.hom.componentInverseImageCommRingIso n).hom.app O' ≫
        ((C'.situation.componentRingedToposHom O' n).comp
          (h.componentRingedToposHom n)).fSharpInverseImage =
      (h.totalRingedToposHom.comp
        (C.situation.componentRingedToposHom O n)).fSharpInverseImage :=
  Morphism.componentRingedToposHom_commutes h.hom h.ringHom n

/-- **Stacks 0DH0, the assertion on sheaves of modules, on underlying sheaves of sets.**
Inverse image to the simplicial component of degree `n` of a direct image of sheaves of modules
along the total morphism is the degreewise direct image of the inverse image to that component.

The comparison is the one of Stacks 0D96 and nothing else: the pullback of modules along a
component inclusion is inverse image on underlying sheaves of sets, by
`CategoryTheory.SimplicialSiteSituation.componentPullbackUnderlyingIso`, and the direct image of
modules is direct image there on the nose. -/
@[stacks 0DH0 "the underlying restriction of the direct image of modules"]
def componentPushforwardModulesForgetIso
    (h : RingedMorphism C C'
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := C.situation.totalTopology)) O)
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := C'.situation.totalTopology)) O'))
    (n : SimplexCategory) :
    h.totalRingedToposHom.pushforwardModules ⋙
        (C'.situation.componentRingedToposHom O' n).toModulesHom.pullbackModules ⋙
          Sheaf.moduleSheafFunctor
            ((Stacks.SheafOfModules.Tensor.ringSheaf
              (J := (C'.situation.componentRingedTopos O' n).J))
              (C'.situation.componentRingedTopos O' n).O) ≅
      (C.situation.componentRingedToposHom O n).toModulesHom.pullbackModules ⋙
        (h.componentRingedToposHom n).pushforwardModules ⋙
          Sheaf.moduleSheafFunctor
            ((Stacks.SheafOfModules.Tensor.ringSheaf
              (J := (C'.situation.componentRingedTopos O' n).J))
              (C'.situation.componentRingedTopos O' n).O) :=
  Functor.isoWhiskerLeft h.totalRingedToposHom.pushforwardModules
      (SimplicialSiteSituation.componentPullbackUnderlyingIso C'.situation O' n) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight h.totalRingedToposHom.pushforwardModulesUnderlyingIso
      (C'.situation.componentRingedToposHom O' n).toToposHom.inverseImage ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft
      (Sheaf.moduleSheafFunctor
        ((Stacks.SheafOfModules.Tensor.ringSheaf (J := (C.situation.totalRingedTopos O).J))
        (C.situation.totalRingedTopos O).O))
      (h.hom.totalPushforwardRestrictIso n) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (SimplicialSiteSituation.componentPullbackUnderlyingIso C.situation O n).symm
      (h.componentRingedToposHom n).toToposHom.pushforward ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (C.situation.componentRingedToposHom O n).toModulesHom.pullbackModules
      (h.componentRingedToposHom n).pushforwardModulesUnderlyingIso.symm

/-! ### The degreewise square as a square of ringed topoi, and sheaves of modules

The source writes the degreewise diagram as an equality of morphisms of ringed topoi. Stacks
04IC reads such an assertion as a 2-isomorphism of the two composites, and that is the form in
which a commuting square of ringed topoi acts on sheaves of modules: the two composite direct
images of sheaves of modules are isomorphic, and so are the two composite pullbacks. The
comparison of the source's last assertion is then the mate of the square of direct images. -/

/-- The composite `h_{total} ∘ g_n` of morphisms of ringed topoi: from the ringed topos of the
simplicial component of degree `n` of the source to the total ringed topos of the target. -/
noncomputable abbrev viaTotalRingedToposHom
    (h : RingedMorphism C C'
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := C.situation.totalTopology)) O)
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := C'.situation.totalTopology)) O'))
    (n : SimplexCategory) :
    RingedToposHom (C.situation.componentRingedTopos O n)
      (C'.situation.totalRingedTopos O') :=
  RingedToposHom.comp (X := C.situation.componentRingedTopos O n)
    (Y := C.situation.totalRingedTopos O) (Z := C'.situation.totalRingedTopos O')
    h.totalRingedToposHom (C.situation.componentRingedToposHom O n)

/-- The composite `g'_n ∘ h_n` of morphisms of ringed topoi: the other side of the degreewise
square of Stacks 0DH0. -/
noncomputable abbrev viaComponentRingedToposHom
    (h : RingedMorphism C C'
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := C.situation.totalTopology)) O)
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := C'.situation.totalTopology)) O'))
    (n : SimplexCategory) :
    RingedToposHom (C.situation.componentRingedTopos O n)
      (C'.situation.totalRingedTopos O') :=
  RingedToposHom.comp (X := C.situation.componentRingedTopos O n)
    (Y := C'.situation.componentRingedTopos O' n) (Z := C'.situation.totalRingedTopos O')
    (C'.situation.componentRingedToposHom O' n) (h.componentRingedToposHom n)

/-- **Stacks 0DH0.** The degreewise square commutes as a square of *ringed* topoi, in the sense
of Stacks 04IC: the two composites `h_{total} ∘ g_n` and `g'_n ∘ h_n` are 2-isomorphic.

The comparison of the direct images is the one of Stacks 0D96, and the compatibility with the
three structure maps is `componentRingedToposHom_commutes` read on underlying sheaves of sets,
through `AlgebraicGeometry.RingedToposHom.TwoIso.ofInverseImageIso`, which transposes a
compatibility of the inverse-image forms into one of the direct-image forms. The underlying
comparison of inverse images is pinned by
`CategoryTheory.CocontinuousSimplicialSite.Morphism.componentInverseImageCommRingIso_forget`,
so this 2-isomorphism is not an arbitrary one. -/
@[stacks 0DH0 "the degreewise square as a 2-isomorphism of ringed topoi"]
noncomputable def componentRingedToposHom_twoIso
    (h : RingedMorphism C C'
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := C.situation.totalTopology)) O)
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := C'.situation.totalTopology)) O'))
    (n : SimplexCategory) :
    RingedToposHom.TwoIso.{u, u, u, u, u, u}
      (viaTotalRingedToposHom h n) (viaComponentRingedToposHom h n) :=
  (RingedToposHom.TwoIso.ofInverseImageIso
    (p := viaComponentRingedToposHom h n) (q := viaTotalRingedToposHom h n)
    (h.hom.componentInverseImageIso n) (by
      have E2 : (C.situation.componentRingedTopos O n).forgetRing.map
            ((h.hom.componentInverseImageCommRingIso n).hom.app O') =
          (h.hom.componentInverseImageIso n).hom.app
            ((C'.situation.totalRingedTopos O').forgetRing.obj
              (C'.situation.totalRingedTopos O').O) :=
        Morphism.componentInverseImageCommRingIso_forget h.hom n O'
      exact (congrArg (fun z ↦ z ≫ (C.situation.componentRingedTopos O n).forgetRing.map
          (viaComponentRingedToposHom h n).fSharpInverseImage) E2).symm.trans
        ((CategoryTheory.Functor.map_comp _ _ _).symm.trans
          (congrArg (C.situation.componentRingedTopos O n).forgetRing.map
            (h.componentRingedToposHom_commutes n))))).symm

/-- **Stacks 0DH0, the degreewise square on direct images of sheaves of modules.** Direct image
to the total ringed topos of the target, taken through the component of degree `n` of the
source, agrees with direct image taken through the component of degree `n` of the target:

`h_{total,*} ∘ g_{n,*} ≅ g'_{n,*} ∘ h_{n,*}` on `Mod(𝒪_n)`.

This is the commuting square of ringed topoi of
`componentRingedToposHom_twoIso` read on sheaves of modules, and it is a genuine module-level
statement: the comparison is additive and linear, not merely a comparison of underlying sheaves
of sets. -/
@[stacks 0DH0 "the commutative squares, on direct images of sheaves of modules"]
noncomputable def componentPushforwardModulesSquareIso
    (h : RingedMorphism C C'
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := C.situation.totalTopology)) O)
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := C'.situation.totalTopology)) O'))
    (n : SimplexCategory) :
    (C.situation.componentRingedToposHom O n).pushforwardModules ⋙
        h.totalRingedToposHom.pushforwardModules ≅
      (h.componentRingedToposHom n).pushforwardModules ⋙
        (C'.situation.componentRingedToposHom O' n).pushforwardModules :=
  (RingedToposHom.pushforwardModulesCompIso (C.situation.componentRingedToposHom O n)
      h.totalRingedToposHom).symm ≪≫
    (componentRingedToposHom_twoIso h n).pushforwardModulesIso ≪≫
    RingedToposHom.pushforwardModulesCompIso (h.componentRingedToposHom n)
      (C'.situation.componentRingedToposHom O' n)

/-- **Stacks 0DH0, the degreewise square on pullbacks of sheaves of modules.** The same square,
read on pullbacks:

`g_n^* ∘ h_{total}^* ≅ h_n^* ∘ (g'_n)^*` on `Mod(𝒪')`.

Both sides are left adjoint to the two sides of `componentPushforwardModulesSquareIso`, so this
is uniqueness of left adjoints applied to that isomorphism. -/
@[stacks 0DH0 "the commutative squares, on pullbacks of sheaves of modules"]
noncomputable def componentPullbackModulesSquareIso
    (h : RingedMorphism C C' (Stacks.SheafOfModules.Tensor.ringSheaf O)
      (Stacks.SheafOfModules.Tensor.ringSheaf O')) (n : SimplexCategory) :
    h.totalRingedToposHom.toModulesHom.pullbackModules ⋙
        (C.situation.componentRingedToposHom O n).toModulesHom.pullbackModules ≅
      (C'.situation.componentRingedToposHom O' n).toModulesHom.pullbackModules ⋙
        (h.componentRingedToposHom n).toModulesHom.pullbackModules :=
  (RingedToposHom.pullbackModulesCompIso (C.situation.componentRingedToposHom O n)
      h.totalRingedToposHom).symm ≪≫
    (componentRingedToposHom_twoIso h n).pullbackModulesIso ≪≫
    RingedToposHom.pullbackModulesCompIso (h.componentRingedToposHom n)
      (C'.situation.componentRingedToposHom O' n)

/-- **Stacks 0DH0, the comparison of the last assertion.** The canonical morphism of functors
`Mod(𝒪) ⟶ Mod(𝒪'_n)`

`(g'_n)^* ∘ h_{total,*} ⟶ h_{n,*} ∘ g_n^*`

attached to the degreewise square: the mate of `componentPushforwardModulesSquareIso` under the
two adjunctions `g_n^* ⊣ g_{n,*}` and `(g'_n)^* ⊣ (g'_n)_*` of Stacks 03D7. The source's last
assertion is that this comparison is invertible, which is
`isIso_componentPushforwardModulesComparison`. -/
@[stacks 0DH0 "the comparison of the last assertion, on sheaves of modules"]
noncomputable def componentPushforwardModulesComparison
    (h : RingedMorphism C C'
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := C.situation.totalTopology)) O)
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := C'.situation.totalTopology)) O'))
    (n : SimplexCategory) :
    h.totalRingedToposHom.pushforwardModules ⋙
        (C'.situation.componentRingedToposHom O' n).toModulesHom.pullbackModules ⟶
      (C.situation.componentRingedToposHom O n).toModulesHom.pullbackModules ⋙
        (h.componentRingedToposHom n).pushforwardModules :=
  (mateEquiv
      (RingedToposHom.pullbackAdjPushforwardModules
        (C.situation.componentRingedToposHom O n))
      (RingedToposHom.pullbackAdjPushforwardModules
        (C'.situation.componentRingedToposHom O' n))).symm
    (TwoSquare.mk _ _ _ _ (componentPushforwardModulesSquareIso h n).hom)

/-- **Stacks 0DH0.** The comparison of the last assertion is pinned by the degreewise square:
its mate under the two adjunctions of Stacks 03D7 is the square of direct images of sheaves of
modules. In particular it is not an arbitrary natural transformation. -/
@[stacks 0DH0 "the comparison of the last assertion is the mate of the square"]
theorem componentPushforwardModulesComparison_mate
    (h : RingedMorphism C C'
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := C.situation.totalTopology)) O)
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := C'.situation.totalTopology)) O'))
    (n : SimplexCategory) :
    mateEquiv
        (RingedToposHom.pullbackAdjPushforwardModules
          (C.situation.componentRingedToposHom O n))
        (RingedToposHom.pullbackAdjPushforwardModules
          (C'.situation.componentRingedToposHom O' n))
        (componentPushforwardModulesComparison h n) =
      TwoSquare.mk _ _ _ _ (componentPushforwardModulesSquareIso h n).hom :=
  Equiv.apply_symm_apply _ _

/-- The comparison of direct images underlying the degreewise 2-isomorphism of ringed topoi is the
inverse of the comparison of Stacks 0D96. -/
theorem componentRingedToposHom_twoIso_e_hom
    (h : RingedMorphism C C'
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := C.situation.totalTopology)) O)
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := C'.situation.totalTopology)) O'))
    (n : SimplexCategory) :
    (componentRingedToposHom_twoIso h n).e.hom = (h.hom.totalComponentPushforwardIso n).inv := by
  change (conjugateIsoEquiv (h.hom.viaComponentMorphism n).adj (h.hom.viaTotalMorphism n).adj
    (h.hom.componentInverseImageIso n)).inv = _
  rw [Morphism.componentInverseImageIso_conjugate]

/-- **Stacks 0DH0, the last assertion: the comparison is invertible.** The canonical comparison
`(g'_n)^* ∘ h_{total,*} ⟶ h_{n,*} ∘ g_n^*` of sheaves of modules is an isomorphism. On
underlying sheaves of sets it is the mate of the degreewise square of topoi, which is invertible
by the Beck–Chevalley property of the square of component inclusions,
`CategoryTheory.CocontinuousSimplicialSite.Morphism.isIso_totalComponentPushforwardMate`; and
the two pullbacks `g_n^*`, `(g'_n)^*` are inverse images on underlying sheaves of sets, so the
module-level mate lies over that one
(`AlgebraicGeometry.RingedToposHom.isIso_mateEquiv_symm_pushforwardModules_of_isIso`). -/
@[stacks 0DH0 "the comparison of the last assertion is invertible"]
instance isIso_componentPushforwardModulesComparison
    (h : RingedMorphism C C'
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := C.situation.totalTopology)) O)
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := C'.situation.totalTopology)) O'))
    (n : SimplexCategory) :
    IsIso (componentPushforwardModulesComparison h n) := by
  have hmate : IsIso ((mateEquiv (C.situation.componentRingedToposHom O n).toToposHom.adj
      (C'.situation.componentRingedToposHom O' n).toToposHom.adj).symm
      (TwoSquare.mk _ _ _ _ (componentRingedToposHom_twoIso h n).e.hom)) := by
    rw [componentRingedToposHom_twoIso_e_hom]
    exact Morphism.isIso_totalComponentPushforwardMate h.hom n
  exact RingedToposHom.isIso_mateEquiv_symm_pushforwardModules_of_isIso
    (C.situation.componentRingedToposHom O n) (C'.situation.componentRingedToposHom O' n)
    (h.componentRingedToposHom n) h.totalRingedToposHom (componentRingedToposHom_twoIso h n)

/-- **Stacks 0DH0, the last assertion, on sheaves of modules.** Inverse image to the simplicial
component of degree `n` of a direct image of sheaves of modules along the total morphism is the
degreewise direct image of the inverse image to that component:

`(g'_n)^* ∘ h_{total,*} ≅ h_{n,*} ∘ g_n^*` as functors `Mod(𝒪) ⟶ Mod(𝒪'_n)`,

the isomorphism being the canonical comparison `componentPushforwardModulesComparison`
attached to the degreewise square, which is invertible by
`isIso_componentPushforwardModulesComparison`. -/
@[stacks 0DH0 "the last assertion, on sheaves of modules"]
noncomputable def componentPushforwardModulesIso
    (h : RingedMorphism C C'
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := C.situation.totalTopology)) O)
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := C'.situation.totalTopology)) O'))
    (n : SimplexCategory) :
    h.totalRingedToposHom.pushforwardModules ⋙
        (C'.situation.componentRingedToposHom O' n).toModulesHom.pullbackModules ≅
      (C.situation.componentRingedToposHom O n).toModulesHom.pullbackModules ⋙
        (h.componentRingedToposHom n).pushforwardModules :=
  asIso (componentPushforwardModulesComparison h n)

end RingedMorphism

end CocontinuousSimplicialSite

end CategoryTheory

end
