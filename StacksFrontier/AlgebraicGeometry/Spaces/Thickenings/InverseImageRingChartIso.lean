module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRingedToposHomInverseImage
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.RingedToposThickeningAdditions
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.RingedToposThickening
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.StructureSheafTransport
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SmallEtaleRingedToposThickening
public import StacksFrontier.CategoryTheory.Sites.Topos.MorphismOfTopoiRingEquivalence

/-!
# The inverse image of a sheaf of rings along a thickening, on étale charts

Let `i : Z ⟶ T` be a morphism of algebraic spaces over a scheme `S` which is a closed immersion
surjective on points — the inclusion of a thickening, up to isomorphism. The direct image of
sheaves of sets along `i` is an equivalence of topoi
(`AlgebraicGeometry.Space.isEquivalence_pushforward_smallEtaleRingedToposHom`). This file draws
the consequence for sheaves of **commutative rings**, in the spelling
`AlgebraicGeometry.Space.smallEtaleInverseImageRing` in which the structure sheaves of the
spaces of a square-zero tower and of a 05ZT realization are compared: for every sheaf of
commutative rings `𝒪` on the small étale site of `T`, the unit `𝒪 ⟶ i_*i⁻¹𝒪` is an isomorphism,
so the sections of `i⁻¹𝒪` over the chart `Z ×_T V` lying under an étale chart `V` of `T` are
the sections of `𝒪` over `V`, naturally in `V`.  At the structure sheaf this reads
`Γ(V, 𝒪_V) ≅ (i⁻¹𝒪_T)(Z ×_T V)`, and the inverse-image structure map `i⁻¹𝒪_T ⟶ 𝒪_Z` becomes the
direct-image one `𝒪_T ⟶ i_*𝒪_Z`.

This is the chart-level identification which a construction of morphisms between two
thickenings of one space from a map of their structure sheaves (the step "`Xₙ ≅ X' ×_Y Yₙ`" of
the proof of [Stacks Project, Tag 0D3X]) is built on.

## Main results

* `MorphismOfTopoi.isIso_ringAdjunction_unit_app`: when the direct image of sheaves of sets
  along a morphism of topoi is an equivalence, the unit of the adjunction between inverse and
  direct image of sheaves of commutative rings is an isomorphism.
* `AlgebraicGeometry.Space.isIso_smallEtaleRingAdjunction_unit_app`: the case of a closed
  immersion of algebraic spaces surjective on points.
* `AlgebraicGeometry.Space.inverseImageRingChartIso`: `𝒪(V) ≅ (i⁻¹𝒪)(Z ×_T V)`, as an
  isomorphism of presheaves of commutative rings on the small étale site of `T`.
* `AlgebraicGeometry.Space.inverseImageRingChartIso_hom_comp_fSharpInverseImage`: the
  inverse-image structure map read through it is the direct-image structure map.

## References

* [Stacks Project, Tag 05ZH](https://stacks.math.columbia.edu/tag/05ZH)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 0D3X](https://stacks.math.columbia.edu/tag/0D3X)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w w' v v' u u'

namespace MorphismOfTopoi

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  (f : MorphismOfTopoi (Sheaf J (Type w)) (Sheaf K (Type w')))

/-- **The unit `𝒪 ⟶ f_*f⁻¹𝒪` of sheaves of commutative rings is an isomorphism** when the direct
image of sheaves of sets along `f` is an equivalence: on underlying sheaves of sets it is the
unit of `f⁻¹ ⊣ f_*`, which is invertible because the left adjoint of an equivalence is fully
faithful, and forgetting the ring structure reflects isomorphisms. -/
theorem isIso_ringAdjunction_unit_app [f.pushforward.IsEquivalence] (O : Sheaf K CommRingCat.{w'}) :
    IsIso (f.ringAdjunction.unit.app O) := by
  have : f.inverseImage.IsEquivalence := f.adj.isEquivalence_left_of_isEquivalence_right
  have : IsIso f.adj.unit := inferInstance
  have h : IsIso ((sheafCompose K (forget CommRingCat.{w'})).map
      (f.ringAdjunction.unit.app O)) := by
    have e := ringAdjunction_homEquiv_forget f O (f.inverseImageRing.obj O) (𝟙 _)
    rw [show f.ringAdjunction.homEquiv O _ (𝟙 _) = f.ringAdjunction.unit.app O from
      Adjunction.homEquiv_id _ _] at e
    simp only [CategoryTheory.Functor.map_id] at e
    rw [e]
    exact (congrArg IsIso (f.adj.homEquiv_id _)).mpr (NatIso.isIso_app_of_isIso f.adj.unit _)
  exact isIso_of_reflects_iso _ (sheafCompose K (forget CommRingCat.{w'}))

end MorphismOfTopoi

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {Z T : AlgebraicSpaces B S hS}

/-- **Along a closed immersion surjective on points, the unit `𝒪 ⟶ i_*i⁻¹𝒪` of sheaves of
commutative rings on the small étale site of the target is an isomorphism.** -/
theorem isIso_smallEtaleRingAdjunction_unit_app (i : Z ⟶ T)
    (hci : IsClosedImmersion B S hS i.hom)
    (hsurj : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf i.hom)
    (O : Sheaf (SmallEtale.topology B S hS T.1) CommRingCat.{u}) :
    IsIso ((smallEtaleRingedToposHom B S hS i).toToposHom.ringAdjunction.unit.app O) :=
  let := isEquivalence_pushforward_smallEtaleRingedToposHom B S hS i hci hsurj
  MorphismOfTopoi.isIso_ringAdjunction_unit_app _ O

/-- **`𝒪(V) ≅ (i⁻¹𝒪)(Z ×_T V)`.** For a closed immersion `i : Z ⟶ T` surjective on points and a
sheaf of commutative rings `𝒪` on the small étale site of `T`, the sections of `𝒪` over an étale
chart `V` of `T` are the sections of `i⁻¹𝒪` over the chart `Z ×_T V` of `Z`, naturally in `V`:
the unit of `i⁻¹ ⊣ i_*` followed by the identification of the direct image along a
representable morphism with restriction along base change of charts (Stacks 03G8). -/
def inverseImageRingChartIso (i : Z ⟶ T) (hci : IsClosedImmersion B S hS i.hom)
    (hsurj : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf i.hom)
    (O : Sheaf (SmallEtale.topology B S hS T.1) CommRingCat.{u}) :
    O.obj ≅ (smallBaseChange B S hS i hci.rep).op ⋙
      ((smallEtaleInverseImageRing B S hS i).obj O).obj :=
  letI := (smallBaseChange_isMorphismOfSites B S hS i hci.rep).toIsContinuous
  letI := isIso_smallEtaleRingAdjunction_unit_app B S hS i hci hsurj O
  (sheafToPresheaf _ _).mapIso
    (asIso ((smallEtaleRingedToposHom B S hS i).toToposHom.ringAdjunction.unit.app O) ≪≫
      (smallEtaleRingedToposHom_representableRing B S hS i hci.rep).app
        ((smallEtaleInverseImageRing B S hS i).obj O))

/-- **The inverse-image structure map read on the charts of the ambient space is the
direct-image one**: `𝒪_T(V) ≅ (i⁻¹𝒪_T)(Z ×_T V) --i♯--> 𝒪_Z(Z ×_T V)` is the structure map
`i♯ : 𝒪_T ⟶ i_*𝒪_Z` read through the identification of the direct image along a representable
morphism with restriction along base change of charts. -/
theorem inverseImageRingChartIso_hom_comp_fSharpInverseImage (i : Z ⟶ T)
    (hci : IsClosedImmersion B S hS i.hom)
    (hsurj : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf i.hom) :
    letI := (smallBaseChange_isMorphismOfSites B S hS i hci.rep).toIsContinuous
    (inverseImageRingChartIso B S hS i hci hsurj (smallEtaleRingedTopos B S hS T).O).hom ≫
        Functor.whiskerLeft (smallBaseChange B S hS i hci.rep).op
          (smallEtaleRingedToposHom B S hS i).fSharpInverseImage.hom =
      ((smallEtaleRingedToposHom B S hS i).fSharp ≫
        (smallEtaleRingedToposHom_representableRing B S hS i hci.rep).hom.app
          (smallEtaleRingedTopos B S hS Z).O).hom := by
  let := (smallBaseChange_isMorphismOfSites B S hS i hci.rep).toIsContinuous
  have hadj : (smallEtaleRingedToposHom B S hS i).toToposHom.ringAdjunction.unit.app _ ≫
      (smallEtaleRingedToposHom B S hS i).toToposHom.pushforwardRing.map
        (smallEtaleRingedToposHom B S hS i).fSharpInverseImage =
      (smallEtaleRingedToposHom B S hS i).fSharp :=
    (Adjunction.homEquiv_unit _ _ _ _).symm.trans (Equiv.apply_symm_apply _ _)
  have hnat := (smallEtaleRingedToposHom_representableRing B S hS i hci.rep).hom.naturality
    (smallEtaleRingedToposHom B S hS i).fSharpInverseImage
  have key : (smallEtaleRingedToposHom B S hS i).toToposHom.ringAdjunction.unit.app _ ≫
      (smallEtaleRingedToposHom_representableRing B S hS i hci.rep).hom.app _ ≫
        ((smallBaseChange B S hS i hci.rep).sheafPushforwardContinuous CommRingCat.{u}
          (SmallEtale.topology B S hS T.1) (SmallEtale.topology B S hS Z.1)).map
          (smallEtaleRingedToposHom B S hS i).fSharpInverseImage =
      (smallEtaleRingedToposHom B S hS i).fSharp ≫
        (smallEtaleRingedToposHom_representableRing B S hS i hci.rep).hom.app
          (smallEtaleRingedTopos B S hS Z).O :=
    calc _ = (smallEtaleRingedToposHom B S hS i).toToposHom.ringAdjunction.unit.app _ ≫
          ((smallEtaleRingedToposHom B S hS i).toToposHom.pushforwardRing.map
            (smallEtaleRingedToposHom B S hS i).fSharpInverseImage ≫
          (smallEtaleRingedToposHom_representableRing B S hS i hci.rep).hom.app _) :=
          congrArg (_ ≫ ·) hnat.symm
      _ = _ := (Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) hadj)
  exact congrArg (fun φ => φ.hom) key

end AlgebraicGeometry.Space

end
