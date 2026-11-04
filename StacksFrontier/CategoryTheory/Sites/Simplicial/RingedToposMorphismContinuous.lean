module

public import StacksFrontier.CategoryTheory.Sites.Simplicial.ContinuousAugmentationSiteFunctors
public import StacksFrontier.CategoryTheory.Sites.Simplicial.RingedMorphismContinuous
public import StacksFrontier.CategoryTheory.Sites.Simplicial.RingedToposMorphism
public import StacksFrontier.CategoryTheory.Sites.Simplicial.TotalContinuousMorphismBaseChange

/-!
# The morphisms of ringed topoi induced by a morphism of ringed simplicial sites, case (A)

A morphism between ringed simplicial sites in case (A) of Stacks 09WE, in the sense of
`CategoryTheory.SimplicialSite.RingedMorphism`, induces a morphism of the total ringed topoi
and, in every simplicial degree, a morphism of the component ringed topoi of Stacks 0D72. The
resulting square of ringed topoi commutes, and on sheaves of modules the inverse image to a
component of a direct image along the total morphism is the degreewise direct image of the
inverse image to that component. This is Stacks 0DH0 in case (A); case (B) is
`StacksFrontier/CategoryTheory/Sites/Simplicial/RingedToposMorphism.lean`, and the two files are
parallel.

## Main definitions

* `CategoryTheory.SimplicialSite.Morphism.componentInverseImageCommRingIso`: the comparison of
  the two inverse images of sheaves of commutative rings around the square of simplicial degree
  `n`, the identification `gₙ⁻¹h_{total}⁻¹𝒪' = hₙ⁻¹𝒪'ₙ` the source uses to define the degreewise
  structure map.
* `CategoryTheory.SimplicialSite.RingedMorphism.totalRingedToposHom`: the induced morphism of
  total ringed topoi.
* `CategoryTheory.SimplicialSite.RingedMorphism.componentRingedToposHom`: the induced morphism of
  component ringed topoi in a given simplicial degree.
* `CategoryTheory.SimplicialSite.RingedMorphism.componentRingedToposHom_twoIso`: the degreewise
  square read as a 2-isomorphism of morphisms of ringed topoi in the sense of Stacks 04IC.
* `CategoryTheory.SimplicialSite.RingedMorphism.componentPushforwardModulesComparison`: the
  canonical comparison `(g'ₙ)^* ∘ h_{total,*} ⟶ h_{n,*} ∘ gₙ^*` of the source's last assertion.

## Main results

* `CategoryTheory.SimplicialSite.RingedMorphism.componentRingedToposHom_commutes`: the square of
  ringed topoi formed by the total morphism, the degreewise morphism and the two component
  morphisms commutes.
* `CategoryTheory.SimplicialSite.RingedMorphism.componentPushforwardModulesSquareIso` and
  `.componentPullbackModulesSquareIso`: the degreewise square on direct images and on pullbacks
  of sheaves of modules.
* `CategoryTheory.SimplicialSite.RingedMorphism.isIso_componentPushforwardModulesComparison` and
  `.componentPushforwardModulesIso`: the source's last assertion on sheaves of modules, the
  canonical comparison `(g'ₙ)^* ∘ h_{total,*} ⟶ h_{n,*} ∘ gₙ^*` is invertible.

## Implementation notes

The homomorphism of structure sheaves of a case-(A) `RingedMorphism` is stored at the level of
sheaves of rings, in the inverse-image form `h_{total}⁻¹𝒪' ⟶ 𝒪` along the continuous functor
`v_total` of total sites; its direct-image form `𝒪' ⟶ h_{total,*}𝒪` is a map into the restriction
of `𝒪` along `v_total`. Since `h_{total,*}` on sheaves of sets *is* restriction along `v_total`,
the structure map of the morphism of total ringed topoi is that direct-image form, read at the
commutative level through the fully faithful forgetful functor and through
`Stacks.Sheaves.ToposPullback.restrictionCommRingIso`, which is the identity on underlying sheaves
of sets. So nothing is chosen.

From there the construction is that of case (B): the degreewise structure map is the inverse
image to the component of the total structure map read through the comparison of inverse images
around the square and the comparisons of structure sheaves of Stacks 0D72; the square of ringed
topoi commutes by cancellation; it is a 2-isomorphism of ringed topoi whose comparison of direct
images is the one of Stacks 0D96 in case (A),
`CategoryTheory.SimplicialSite.Morphism.totalComponentPushforwardIso`; and the comparison of the
last assertion is the mate of the square of direct images of sheaves of modules, invertible
because on underlying sheaves of sets it lies over the mate of the square of topoi, which is
invertible by `CategoryTheory.SimplicialSite.Morphism.isIso_totalComponentPushforwardMate`.

## References

* [Stacks Project, Tag 0DH0](https://stacks.math.columbia.edu/tag/0DH0)
* [Stacks Project, Tag 0DGZ](https://stacks.math.columbia.edu/tag/0DGZ)
* [Stacks Project, Tag 0D96](https://stacks.math.columbia.edu/tag/0D96)
* [Stacks Project, Tag 0D72](https://stacks.math.columbia.edu/tag/0D72)
* [Stacks Project, Tag 09WE](https://stacks.math.columbia.edu/tag/09WE)
* [Stacks Project, Tag 04IC](https://stacks.math.columbia.edu/tag/04IC)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

universe u

namespace CategoryTheory

attribute [local instance] SimplicialSiteSituation.hasWeakSheafifyComponent
  wEqualsLocallyBijectiveComponent

namespace SimplicialSite

namespace Morphism

variable {C C' : SimplicialSite.{u}}

/-- The morphism of topoi from the component of simplicial degree `n` of the source to the total
topos of the target, through the total topos of the source. -/
abbrev viaTotalMorphism (h : SimplicialSite.Morphism C C') (n : SimplexCategory) :
    MorphismOfTopoi (Sheaf (C.situation.componentTopology n) (Type u))
      (Sheaf C'.situation.totalTopology (Type u)) :=
  h.totalMorphism.comp (SimplicialSiteSituation.componentMorphism C.situation n)

/-- The morphism of topoi from the component of simplicial degree `n` of the source to the total
topos of the target, through the component of simplicial degree `n` of the target. -/
abbrev viaComponentMorphism (h : SimplicialSite.Morphism C C') (n : SimplexCategory) :
    MorphismOfTopoi (Sheaf (C.situation.componentTopology n) (Type u))
      (Sheaf C'.situation.totalTopology (Type u)) :=
  (SimplicialSiteSituation.componentMorphism C'.situation n).comp
    ((SimplicialSiteMorphism.ofMorphismOfSites h).componentMorphism n)

/-- The comparison of the two inverse images of sheaves of sets around the square of simplicial
degree `n`, obtained by conjugating the comparison of direct images of Stacks 0D96 along the two
adjunctions. -/
def componentInverseImageIso (h : SimplicialSite.Morphism C C') (n : SimplexCategory) :
    (viaTotalMorphism h n).inverseImage ≅ (viaComponentMorphism h n).inverseImage :=
  (conjugateIsoEquiv (viaComponentMorphism h n).adj (viaTotalMorphism h n).adj).symm
    (h.totalComponentPushforwardIso n)

/-- The comparison of inverse images is the conjugate of the comparison of direct images of
Stacks 0D96, so it is not an arbitrary isomorphism of inverse images. -/
theorem componentInverseImageIso_conjugate (h : SimplicialSite.Morphism C C')
    (n : SimplexCategory) :
    conjugateIsoEquiv (viaComponentMorphism h n).adj (viaTotalMorphism h n).adj
        (componentInverseImageIso h n) =
      h.totalComponentPushforwardIso n :=
  Equiv.apply_symm_apply _ _

/-- **Stacks 0DH0**, case (A). The comparison of the two inverse images of sheaves of
commutative rings around the square of simplicial degree `n`: the identification
`gₙ⁻¹h_{total}⁻¹𝒪' = hₙ⁻¹(g'ₙ)⁻¹𝒪'` through which the source defines the degreewise structure
map. -/
@[stacks 0DH0 "the canonical ring comparison, case (A)"]
def componentInverseImageCommRingIso (h : SimplicialSite.Morphism C C') (n : SimplexCategory) :
    inverseImageCommRingFunctor.{u, u, u, u, u, u} (viaTotalMorphism h n) ≅
      inverseImageCommRingFunctor.{u, u, u, u, u, u} (viaComponentMorphism h n) :=
  pullbackCommRingSheafFunctorIsoOfNatIso.{u, u, u, u, u, u}
    (C.situation.componentTopology n)
    (Φ := (viaTotalMorphism h n).inverseImage)
    (Φ' := (viaComponentMorphism h n).inverseImage) (componentInverseImageIso h n)

/-- **Stacks 0DH0**, case (A). The comparison of inverse images of sheaves of commutative rings
has the comparison of inverse images of sheaves of sets as its underlying map. -/
@[stacks 0DH0 "the canonical underlying comparison, case (A)"]
theorem componentInverseImageCommRingIso_forget (h : SimplicialSite.Morphism C C')
    (n : SimplexCategory) (O' : Sheaf C'.situation.totalTopology CommRingCat.{u}) :
    (sheafCompose (C.situation.componentTopology n) (forget CommRingCat.{u})).map
        ((componentInverseImageCommRingIso h n).hom.app O') =
      (componentInverseImageIso h n).hom.app
        ((sheafCompose C'.situation.totalTopology (forget CommRingCat.{u})).obj O') :=
  rfl

end Morphism

/-- The underlying sheaf of rings, on the total site of a simplicial site in case (A), of a sheaf
of commutative rings on the total site of its simplicial-site situation. The two total sites are
the same by definition; this names the passage from the one spelling to the other, so that a
morphism between ringed simplicial sites, which is stated on the total site of the simplicial
site, can be taken between the structure sheaves of the total ringed topoi. -/
def totalRingSheaf (C : SimplicialSite.{u}) (O : Sheaf C.situation.totalTopology CommRingCat.{u}) :
    Sheaf C.totalTopology RingCat.{u} :=
  (Stacks.SheafOfModules.Tensor.ringSheaf (J := C.situation.totalTopology)) O

namespace RingedMorphism

variable {C C' : SimplicialSite.{u}}
  {O : Sheaf C.situation.totalTopology CommRingCat.{u}}
  {O' : Sheaf C'.situation.totalTopology CommRingCat.{u}}

/-- The homomorphism of structure sheaves of a morphism between ringed simplicial sites in case
(A), in the direct-image form `𝒪' ⟶ h_{total,*}𝒪` of the morphism of total topoi, at the
commutative level. It is the direct-image form `ringHomPushforward` read through full
faithfulness of forgetting commutativity and through the identification of the direct image of
a sheaf of commutative rings along restriction with its restriction, which is the identity on
underlying sheaves of sets. -/
def totalFSharp
    (h : RingedMorphism C C' (C.totalRingSheaf O) (C'.totalRingSheaf O')) :
    O' ⟶ (pushforwardCommRingFunctor h.hom.totalMorphism).obj O :=
  let := h.hom.totalFunctor_isContinuous
  (fullyFaithfulForgetCommRingSheaf C'.totalTopology).preimage
      (X := O')
      (Y := (h.hom.totalFunctor.sheafPushforwardContinuous CommRingCat.{u} C'.totalTopology
        C.totalTopology).obj O) h.ringHomPushforward ≫
    (restrictionCommRingIso C'.totalTopology C.totalTopology h.hom.totalFunctor O).inv

/-- **Stacks 0DH0**, case (A). The morphism of total ringed topoi induced by a morphism between
ringed simplicial sites. -/
@[stacks 0DH0 "the total morphism of ringed topoi, case (A)"]
def totalRingedToposHom
    (h : RingedMorphism C C' (C.totalRingSheaf O) (C'.totalRingSheaf O')) :
    RingedToposHom (C.situation.totalRingedTopos O) (C'.situation.totalRingedTopos O') where
  toToposHom := h.hom.totalMorphism
  fSharp := h.totalFSharp

/-- The underlying geometric morphism of the total morphism of ringed topoi is the morphism of
total topoi of Stacks 0D96. -/
theorem totalRingedToposHom_toToposHom
    (h : RingedMorphism C C' (C.totalRingSheaf O) (C'.totalRingSheaf O')) :
    h.totalRingedToposHom.toToposHom = h.hom.totalMorphism :=
  rfl

/-- The structure map of the degreewise morphism of ringed topoi, in inverse-image form: the
inverse image to the component of the total structure map, read through the comparison of inverse
images around the degreewise square and the comparisons of structure sheaves of Stacks 0D72. -/
def componentFSharpInverseImage
    (h : RingedMorphism C C' (C.totalRingSheaf O) (C'.totalRingSheaf O')) (n : SimplexCategory) :
    (inverseImageCommRingFunctor
        ((SimplicialSiteMorphism.ofMorphismOfSites h.hom).componentMorphism n)).obj
          ((C'.situation.componentRingedTopos O' n).O) ⟶
      (C.situation.componentRingedTopos O n).O :=
  (inverseImageCommRingFunctor
      ((SimplicialSiteMorphism.ofMorphismOfSites h.hom).componentMorphism n)).map
        ((SimplicialSiteSituation.componentRingedTopos_restrictionIso C'.situation n).inv.app O') ≫
    (inverseImageCommRingComp (SimplicialSiteSituation.componentMorphism C'.situation n)
      ((SimplicialSiteMorphism.ofMorphismOfSites h.hom).componentMorphism n)).hom.app O' ≫
    (h.hom.componentInverseImageCommRingIso n).inv.app O' ≫
    (inverseImageCommRingComp h.hom.totalMorphism
      (SimplicialSiteSituation.componentMorphism C.situation n)).inv.app O' ≫
    (inverseImageCommRingFunctor
      (SimplicialSiteSituation.componentMorphism C.situation n)).map
        h.totalRingedToposHom.fSharpInverseImage ≫
    (SimplicialSiteSituation.componentRingedTopos_restrictionIso C.situation n).hom.app O

/-- **Stacks 0DH0**, case (A). The morphism of component ringed topoi in simplicial degree `n`
induced by a morphism between ringed simplicial sites. -/
@[stacks 0DH0 "the component morphisms of ringed topoi, case (A)"]
def componentRingedToposHom
    (h : RingedMorphism C C' (C.totalRingSheaf O) (C'.totalRingSheaf O')) (n : SimplexCategory) :
    RingedToposHom (C.situation.componentRingedTopos O n)
      (C'.situation.componentRingedTopos O' n) where
  toToposHom := (SimplicialSiteMorphism.ofMorphismOfSites h.hom).componentMorphism n
  fSharp :=
    (commRingImageAdjunction
        ((SimplicialSiteMorphism.ofMorphismOfSites h.hom).componentMorphism n)).homEquiv
      ((C'.situation.componentRingedTopos O' n).O)
      ((C.situation.componentRingedTopos O n).O)
      (h.componentFSharpInverseImage n)

/-- **Stacks 0DH0**, case (A). The underlying geometric morphism of the degreewise morphism of
ringed topoi is the component morphism of topoi of Stacks 0D95. -/
@[stacks 0DH0 "the underlying degreewise geometric morphisms, case (A)"]
theorem componentRingedToposHom_toToposHom
    (h : RingedMorphism C C' (C.totalRingSheaf O) (C'.totalRingSheaf O')) (n : SimplexCategory) :
    (h.componentRingedToposHom n).toToposHom =
      (SimplicialSiteMorphism.ofMorphismOfSites h.hom).componentMorphism n :=
  rfl

/-- The structure map of the degreewise morphism of ringed topoi is the prescribed one. -/
theorem componentRingedToposHom_fSharpInverseImage
    (h : RingedMorphism C C' (C.totalRingSheaf O) (C'.totalRingSheaf O')) (n : SimplexCategory) :
    (h.componentRingedToposHom n).fSharpInverseImage = h.componentFSharpInverseImage n :=
  Equiv.symm_apply_apply _ _

/-- **Stacks 0DH0**, case (A). The square of ringed topoi formed by the total morphism, the
degreewise morphism and the two canonical morphisms from the components of simplicial degree `n`
commutes: the comparison of inverse images identifies the two composite structure maps. -/
@[stacks 0DH0 "the commutative squares of ringed topoi, case (A)"]
theorem componentRingedToposHom_commutes
    (h : RingedMorphism C C' (C.totalRingSheaf O) (C'.totalRingSheaf O')) (n : SimplexCategory) :
    (h.hom.componentInverseImageCommRingIso n).hom.app O' ≫
        ((C'.situation.componentRingedToposHom O' n).comp
          (h.componentRingedToposHom n)).fSharpInverseImage =
      (h.totalRingedToposHom.comp
        (C.situation.componentRingedToposHom O n)).fSharpInverseImage := by
  have hc :
      (inverseImageCommRingFunctor
            ((SimplicialSiteMorphism.ofMorphismOfSites h.hom).componentMorphism n)).map
          ((SimplicialSiteSituation.componentRingedTopos_restrictionIso
            C'.situation n).hom.app O') ≫
        (inverseImageCommRingFunctor
            ((SimplicialSiteMorphism.ofMorphismOfSites h.hom).componentMorphism n)).map
          ((SimplicialSiteSituation.componentRingedTopos_restrictionIso
            C'.situation n).inv.app O') = 𝟙 _ := by
    rw [← Functor.map_comp, Iso.hom_inv_id_app, Functor.map_id]
  have cancel₃ : ∀ {D : Type (u + 1)} [Category.{u} D] {W X Y Z T : D}
      (a : W ⟶ X) (a' : X ⟶ W) (b : X ⟶ Y) (b' : Y ⟶ X) (c : Y ⟶ Z) (c' : Z ⟶ Y),
      c ≫ c' = 𝟙 Y → b ≫ b' = 𝟙 X → a ≫ a' = 𝟙 W → ∀ k : W ⟶ T,
      a ≫ b ≫ c ≫ c' ≫ b' ≫ a' ≫ k = k := by
    intro D _ W X Y Z T a a' b b' c c' hc hb ha k
    rw [← Category.assoc c c', hc, Category.id_comp, ← Category.assoc b b', hb,
      Category.id_comp, ← Category.assoc a a', ha, Category.id_comp]
  rw [RingedToposHom.comp_fSharpInverseImage, RingedToposHom.comp_fSharpInverseImage]
  simp only [RingedToposHom.compFSharpInverseImage,
    componentRingedToposHom_fSharpInverseImage,
    SimplicialSiteSituation.componentRingedToposHom_fSharpInverseImage,
    componentFSharpInverseImage,
    componentRingedToposHom_toToposHom, totalRingedToposHom_toToposHom,
    SimplicialSiteSituation.componentRingedToposHom_toToposHom,
    SimplicialSiteSituation.totalRingedTopos_O]
  exact cancel₃ _ _ _ _ _ _ hc
    ((inverseImageCommRingComp (SimplicialSiteSituation.componentMorphism C'.situation n)
      ((SimplicialSiteMorphism.ofMorphismOfSites h.hom).componentMorphism n)).inv_hom_id_app O')
    ((h.hom.componentInverseImageCommRingIso n).hom_inv_id_app O') _

/-! ### The degreewise square as a square of ringed topoi, and sheaves of modules -/

/-- The composite `h_{total} ∘ g_n` of morphisms of ringed topoi. -/
noncomputable abbrev viaTotalRingedToposHom
    (h : RingedMorphism C C' (C.totalRingSheaf O) (C'.totalRingSheaf O')) (n : SimplexCategory) :
    RingedToposHom (C.situation.componentRingedTopos O n)
      (C'.situation.totalRingedTopos O') :=
  RingedToposHom.comp (X := C.situation.componentRingedTopos O n)
    (Y := C.situation.totalRingedTopos O) (Z := C'.situation.totalRingedTopos O')
    h.totalRingedToposHom (C.situation.componentRingedToposHom O n)

/-- The composite `g'_n ∘ h_n` of morphisms of ringed topoi. -/
noncomputable abbrev viaComponentRingedToposHom
    (h : RingedMorphism C C' (C.totalRingSheaf O) (C'.totalRingSheaf O')) (n : SimplexCategory) :
    RingedToposHom (C.situation.componentRingedTopos O n)
      (C'.situation.totalRingedTopos O') :=
  RingedToposHom.comp (X := C.situation.componentRingedTopos O n)
    (Y := C'.situation.componentRingedTopos O' n) (Z := C'.situation.totalRingedTopos O')
    (C'.situation.componentRingedToposHom O' n) (h.componentRingedToposHom n)

/-- **Stacks 0DH0**, case (A). The degreewise square commutes as a square of *ringed* topoi, in
the sense of Stacks 04IC: the two composites `h_{total} ∘ g_n` and `g'_n ∘ h_n` are
2-isomorphic, the comparison of direct images being the one of Stacks 0D96. -/
@[stacks 0DH0 "the degreewise square as a 2-isomorphism of ringed topoi, case (A)"]
noncomputable def componentRingedToposHom_twoIso
    (h : RingedMorphism C C' (C.totalRingSheaf O) (C'.totalRingSheaf O')) (n : SimplexCategory) :
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

/-- **Stacks 0DH0**, case (A), the degreewise square on direct images of sheaves of modules:
`h_{total,*} ∘ g_{n,*} ≅ g'_{n,*} ∘ h_{n,*}` on `Mod(𝒪_n)`. -/
@[stacks 0DH0 "the commutative squares, on direct images of sheaves of modules, case (A)"]
noncomputable def componentPushforwardModulesSquareIso
    (h : RingedMorphism C C' (C.totalRingSheaf O) (C'.totalRingSheaf O')) (n : SimplexCategory) :
    (C.situation.componentRingedToposHom O n).pushforwardModules ⋙
        h.totalRingedToposHom.pushforwardModules ≅
      (h.componentRingedToposHom n).pushforwardModules ⋙
        (C'.situation.componentRingedToposHom O' n).pushforwardModules :=
  (RingedToposHom.pushforwardModulesCompIso (C.situation.componentRingedToposHom O n)
      h.totalRingedToposHom).symm ≪≫
    (componentRingedToposHom_twoIso h n).pushforwardModulesIso ≪≫
    RingedToposHom.pushforwardModulesCompIso (h.componentRingedToposHom n)
      (C'.situation.componentRingedToposHom O' n)

/-- **Stacks 0DH0**, case (A), the degreewise square on pullbacks of sheaves of modules:
`g_n^* ∘ h_{total}^* ≅ h_n^* ∘ (g'_n)^*` on `Mod(𝒪')`. -/
@[stacks 0DH0 "the commutative squares, on pullbacks of sheaves of modules, case (A)"]
noncomputable def componentPullbackModulesSquareIso
    (h : RingedMorphism C C' (C.totalRingSheaf O) (C'.totalRingSheaf O')) (n : SimplexCategory) :
    h.totalRingedToposHom.toModulesHom.pullbackModules ⋙
        (C.situation.componentRingedToposHom O n).toModulesHom.pullbackModules ≅
      (C'.situation.componentRingedToposHom O' n).toModulesHom.pullbackModules ⋙
        (h.componentRingedToposHom n).toModulesHom.pullbackModules :=
  (RingedToposHom.pullbackModulesCompIso (C.situation.componentRingedToposHom O n)
      h.totalRingedToposHom).symm ≪≫
    (componentRingedToposHom_twoIso h n).pullbackModulesIso ≪≫
    RingedToposHom.pullbackModulesCompIso (h.componentRingedToposHom n)
      (C'.situation.componentRingedToposHom O' n)

/-- **Stacks 0DH0**, case (A), the comparison of the last assertion: the canonical morphism of
functors `Mod(𝒪) ⟶ Mod(𝒪'_n)`

`(g'_n)^* ∘ h_{total,*} ⟶ h_{n,*} ∘ g_n^*`,

the mate of `componentPushforwardModulesSquareIso` under the two adjunctions `g_n^* ⊣ g_{n,*}`
and `(g'_n)^* ⊣ (g'_n)_*` of Stacks 03D7. -/
@[stacks 0DH0 "the comparison of the last assertion, on sheaves of modules, case (A)"]
noncomputable def componentPushforwardModulesComparison
    (h : RingedMorphism C C' (C.totalRingSheaf O) (C'.totalRingSheaf O')) (n : SimplexCategory) :
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

/-- **Stacks 0DH0**, case (A). The comparison of the last assertion is pinned by the degreewise
square: its mate under the two adjunctions of Stacks 03D7 is the square of direct images of
sheaves of modules. -/
@[stacks 0DH0 "the comparison of the last assertion is the mate of the square, case (A)"]
theorem componentPushforwardModulesComparison_mate
    (h : RingedMorphism C C' (C.totalRingSheaf O) (C'.totalRingSheaf O')) (n : SimplexCategory) :
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
    (h : RingedMorphism C C' (C.totalRingSheaf O) (C'.totalRingSheaf O')) (n : SimplexCategory) :
    (componentRingedToposHom_twoIso h n).e.hom = (h.hom.totalComponentPushforwardIso n).inv := by
  show (conjugateIsoEquiv (h.hom.viaComponentMorphism n).adj (h.hom.viaTotalMorphism n).adj
    (h.hom.componentInverseImageIso n)).inv = _
  rw [Morphism.componentInverseImageIso_conjugate]

/-- **Stacks 0DH0**, case (A), the last assertion: the comparison is invertible. On underlying
sheaves of sets it is the mate of the degreewise square of topoi, which is invertible by
`CategoryTheory.SimplicialSite.Morphism.isIso_totalComponentPushforwardMate`. -/
@[stacks 0DH0 "the comparison of the last assertion is invertible, case (A)"]
instance isIso_componentPushforwardModulesComparison
    (h : RingedMorphism C C' (C.totalRingSheaf O) (C'.totalRingSheaf O')) (n : SimplexCategory) :
    IsIso (componentPushforwardModulesComparison h n) := by
  have hmate : IsIso ((mateEquiv (C.situation.componentRingedToposHom O n).toToposHom.adj
      (C'.situation.componentRingedToposHom O' n).toToposHom.adj).symm
      (TwoSquare.mk _ _ _ _ (componentRingedToposHom_twoIso h n).e.hom)).natTrans := by
    rw [componentRingedToposHom_twoIso_e_hom]
    exact Morphism.isIso_totalComponentPushforwardMate h.hom n
  exact RingedToposHom.isIso_mateEquiv_symm_pushforwardModules_of_isIso
    (C.situation.componentRingedToposHom O n) (C'.situation.componentRingedToposHom O' n)
    (h.componentRingedToposHom n) h.totalRingedToposHom (componentRingedToposHom_twoIso h n)

/-- **Stacks 0DH0**, case (A), the last assertion, on sheaves of modules:

`(g'_n)^* ∘ h_{total,*} ≅ h_{n,*} ∘ g_n^*` as functors `Mod(𝒪) ⟶ Mod(𝒪'_n)`,

the isomorphism being the canonical comparison `componentPushforwardModulesComparison`. -/
@[stacks 0DH0 "the last assertion, on sheaves of modules, case (A)"]
noncomputable def componentPushforwardModulesIso
    (h : RingedMorphism C C' (C.totalRingSheaf O) (C'.totalRingSheaf O')) (n : SimplexCategory) :
    h.totalRingedToposHom.pushforwardModules ⋙
        (C'.situation.componentRingedToposHom O' n).toModulesHom.pullbackModules ≅
      (C.situation.componentRingedToposHom O n).toModulesHom.pullbackModules ⋙
        (h.componentRingedToposHom n).pushforwardModules :=
  asIso (componentPushforwardModulesComparison h n)

end RingedMorphism

end SimplicialSite

end CategoryTheory

end
