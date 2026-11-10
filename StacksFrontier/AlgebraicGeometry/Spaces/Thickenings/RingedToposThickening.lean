module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Pushout.ThickeningPushout
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionStructureMap
public import StacksFrontier.AlgebraicGeometry.Spaces.ThickeningMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.EtaleTopos
public import StacksFrontier.Deformation.ToposThickening.MorphismOfThickenings

/-!
# The structure map of the small étale ringed topoi of a thickening of algebraic spaces

Let `i : Z ⟶ Z'` be a morphism of algebraic spaces over a scheme `S` which is a closed
immersion, and let

`i_{small} : (Sh(Z_étale), 𝒪_Z) ⟶ (Sh(Z'_étale), 𝒪_{Z'})`

be the associated morphism of small étale ringed topoi of Stacks 03G8. This module studies its
structure map `i^♯`: it is locally surjective, and when `i` is moreover surjective (a
thickening) its kernel consists of nilpotent sections on affine charts and is locally
nilpotent. These are two of the three conditions of a thickening of ringed topoi in the sense
of Stacks 08M7, the inputs of the implication (1) ⇒ (2) of Stacks 0D16.

## Main results

* `AlgebraicGeometry.Space.isNilpotent_of_fSharp_app_eq_zero_of_isAffine`: for a surjective
  closed immersion, a section over an affine étale chart killed by the structure map is
  nilpotent.
* `AlgebraicGeometry.Space.isLocallySurjective_fSharp`: the structure map of the morphism of
  ringed topoi of a closed immersion is locally surjective.
* `AlgebraicGeometry.Space.hasLocallyNilpotentKernel_smallEtaleRingedToposHom`: for a surjective
  closed immersion the kernel of that structure map is locally nilpotent.

## Implementation notes

*Surjectivity of the structure map* is Stacks 03MB,
`AlgebraicGeometry.Space.isLocallySurjective_structureSharp`, transported from the structure map
of sheaves of *rings* to the structure map of the morphism of ringed topoi, which is a map of
sheaves of *commutative* rings with the same underlying map of sheaves of sets by
`AlgebraicGeometry.Space.forgetCommRingSheaf_map_fSharp`.

*Local nilpotence of the kernel.* A section of `𝒪_{Z'}` over an étale chart killed by the
structure map is killed, chart by chart, by pullback of regular functions along the cartesian
projection `Z ×_{Z'} V ⟶ V` (`AlgebraicGeometry.Space.chartProjection_structureMapApp` at the
base-changed chart). Over an *affine* chart that projection is a thickening of schemes — a
closed immersion, surjective — so the section is nilpotent by
`Stacks.Thickenings.IsThickening.isNilpotent_of_mem_ker_appTop`. The affine charts are a dense
subsite of the small étale site, so every chart is covered by them, and a restriction of a
nilpotent section is nilpotent. The structure map `i^♯` is built against
`AlgebraicGeometry.Space.smallEtaleDirectImage` while the chart formula computes the right Kan
extension form, and the two differ by the isomorphism
`AlgebraicGeometry.Space.smallEtaleDirectImageRanIso`, which is injective on sections.

## References

* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB)
* [Stacks Project, Tag 08M7](https://stacks.math.columbia.edu/tag/08M7)
* [Stacks Project, Tag 0D16](https://stacks.math.columbia.edu/tag/0D16)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf Opposite
open Stacks.Sheaves.ToposPullback

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {Z Z' : AlgebraicSpaces B S hS}

/-! ### The structure map on sections -/

/-- The comparison between the two forms of the small étale direct image is injective on
sections over an étale chart: on underlying sheaves of sets it is a component of an isomorphism
of functors, and forgetting the ring structure is faithful. -/
private theorem injective_directImageComparison_app (i : Z ⟶ Z')
    (V : SmallEtale B S hS Z'.1) :
    Function.Injective ((pullbackRingSheafMapOfNatTrans
      (SmallEtale.topology B S hS Z'.1) (structureRingSheaf B S hS Z)
      (smallEtaleDirectImageRanIso B S hS i).inv).hom.app (op V)).hom := by
  have hforget : Mono ((sheafCompose (SmallEtale.topology B S hS Z'.1)
      (forget RingCat.{u})).map (pullbackRingSheafMapOfNatTrans
        (SmallEtale.topology B S hS Z'.1) (structureRingSheaf B S hS Z)
        (smallEtaleDirectImageRanIso B S hS i).inv)) := by
    rw [ringSheafMap_pullbackRingSheafMapOfNatTrans]
    change Mono (((smallEtaleDirectImageRanIso B S hS i).app
      (structureRingSheaf B S hS Z).ringSheaf).symm.hom)
    infer_instance
  have hmono : Mono (pullbackRingSheafMapOfNatTrans (SmallEtale.topology B S hS Z'.1)
      (structureRingSheaf B S hS Z) (smallEtaleDirectImageRanIso B S hS i).inv) :=
    (sheafCompose (SmallEtale.topology B S hS Z'.1) (forget RingCat.{u})).mono_of_mono_map hforget
  exact (mono_iff_app_injective_ringCat _ _).mp hmono (op V)

/-- A section of `𝒪_{Z'}` over an étale chart killed by the structure map `i^♯` of the morphism
of small étale ringed topoi is killed by the structure map on sections of Stacks 03G8.

The two differ by the comparison of the two forms of the direct image, which is injective on
sections by `AlgebraicGeometry.Space.injective_directImageComparison_app`, and by forgetting
commutativity, which `AlgebraicGeometry.Space.forgetCommRingSheaf_map_fSharp` undoes. -/
theorem structureMapApp_eq_zero_of_fSharp_app_eq_zero (i : Z ⟶ Z')
    (V : SmallEtale B S hS Z'.1)
    (a : ToType ((structureRingSheaf B S hS Z').obj.obj (op V)))
    (ha : (smallEtaleRingedToposHom B S hS i).fSharp.hom.app (op V) a = 0) :
    structureMapApp B S hS i V a =
      structureMapApp B S hS i V
        (0 : ToType ((structureRingSheaf B S hS Z').obj.obj (op V))) := by
  have hsharp : (structureSharp B S hS i).hom.app (op V) a = 0 := by
    rw [← forgetCommRingSheaf_map_fSharp B S hS i]
    exact ha
  have key : ∀ x : ToType ((structureRingSheaf B S hS Z').obj.obj (op V)),
      ((pullbackRingSheafMapOfNatTrans (SmallEtale.topology B S hS Z'.1)
          (structureRingSheaf B S hS Z)
          (smallEtaleDirectImageRanIso B S hS i).inv).hom.app (op V)).hom
            (structureMapApp B S hS i V x) =
        (structureSharp B S hS i).hom.app (op V) x := fun _ ↦ rfl
  refine injective_directImageComparison_app B S hS i V ?_
  rw [key a, key (0 : ToType ((structureRingSheaf B S hS Z').obj.obj (op V))), hsharp]
  exact (map_zero _).symm

/-! ### Local nilpotence of the kernel of the structure map -/

/-- **A section over an affine étale chart killed by the structure map of a surjective closed
immersion is nilpotent.** Let `i : Z ⟶ Z'` be a closed immersion of algebraic spaces over `S`
which is surjective, and let `V` be an étale scheme chart of `Z'` whose underlying scheme is
affine. A section of `𝒪_{Z'}` over `V` killed by `i^♯` is nilpotent.

The structure map on sections projects, at the base-changed chart, to pullback of regular
functions along the cartesian projection `Z ×_{Z'} V ⟶ V`
(`AlgebraicGeometry.Space.chartProjection_structureMapApp`), so the section pulls back to zero
along that projection. The projection is a closed immersion because `i` is, and surjective
because `i` is, so it is a thickening of schemes with affine target and
`Stacks.Thickenings.IsThickening.isNilpotent_of_mem_ker_appTop` applies. -/
theorem isNilpotent_of_fSharp_app_eq_zero_of_isAffine (i : Z ⟶ Z')
    (hci : IsClosedImmersion B S hS i.hom)
    (hsurj : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf i.hom)
    (V : SmallEtale B S hS Z'.1)
    (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj V.1.left))
    (a : ToType ((structureRingSheaf B S hS Z').obj.obj (op V)))
    (ha : (smallEtaleRingedToposHom B S hS i).fSharp.hom.app (op V) a = 0) :
    IsNilpotent a := by
  have := hV
  have hthick : Stacks.Thickenings.IsThickening
      ((BigFppfOver.toScheme B S hS).map (hci.rep.snd V.1.hom)) :=
    ⟨hci.property_snd V.1.hom, (hsurj.property_snd V.1.hom).surj⟩
  have hma := structureMapApp_eq_zero_of_fSharp_app_eq_zero B S hS i V a ha
  have hpull : chartPullback B S hS i V (chartBaseChangeArrow B S hS i hci.rep V) a =
      chartPullback B S hS i V (chartBaseChangeArrow B S hS i hci.rep V)
        (0 : ToType ((structureRingSheaf B S hS Z').obj.obj (op V))) := by
    rw [← chartProjection_structureMapApp B S hS i V
        (chartBaseChangeArrow B S hS i hci.rep V) a,
      ← chartProjection_structureMapApp B S hS i V
        (chartBaseChangeArrow B S hS i hci.rep V)
        (0 : ToType ((structureRingSheaf B S hS Z').obj.obj (op V))), hma]
  have hzero : chartPullback B S hS i V (chartBaseChangeArrow B S hS i hci.rep V)
      (0 : ToType ((structureRingSheaf B S hS Z').obj.obj (op V))) =
      (0 : ToType ((structureRingSheaf B S hS Z).obj.obj
        (chartBaseChangeArrow B S hS i hci.rep V).right)) :=
    (chartPullbackRingHom B S hS i V (chartBaseChangeArrow B S hS i hci.rep V)).map_zero
  rw [hzero, chartPullback, chartBaseChangeMap_chartBaseChangeArrow, Scheme.Γ_map_op] at hpull
  exact hthick.isNilpotent_of_mem_ker_appTop (RingHom.mem_ker.mpr hpull)

/-- **The kernel of the structure map of a surjective closed immersion is locally nilpotent.**
For a closed immersion `i : Z ⟶ Z'` of algebraic spaces over `S` which is surjective, every
section of `𝒪_{Z'}` killed by the structure map of the morphism of small étale ringed topoi
becomes nilpotent on a covering sieve: on the sieve of arrows factoring through an affine étale
chart, which is covering because the affine étale charts are a dense subsite of the small étale
site (Stacks 04JS).

Over an affine chart the section is nilpotent by
`AlgebraicGeometry.Space.isNilpotent_of_fSharp_app_eq_zero_of_isAffine`, and any further
restriction of it is the image of a nilpotent section under a ring homomorphism. -/
theorem hasLocallyNilpotentKernel_smallEtaleRingedToposHom (i : Z ⟶ Z')
    (hci : IsClosedImmersion B S hS i.hom)
    (hsurj : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf i.hom) :
    Deformation.ToposThickening.HasLocallyNilpotentKernel
      (X := smallEtaleRingedTopos B S hS Z) (Y := smallEtaleRingedTopos B S hS Z')
      (smallEtaleRingedToposHom B S hS i) := by
  let _ : (AffineEtale.inclusion B S hS Z'.1).IsCoverDense
      (SmallEtale.topology B S hS Z'.1) :=
    (AffineEtale.inclusion_isSpecialCocontinuous B S hS Z'.1 Z'.2).2.isCoverDense'
  intro U a ha
  refine ⟨Sieve.coverByImage (AffineEtale.inclusion B S hS Z'.1) U.unop,
    (AffineEtale.inclusion B S hS Z'.1).is_cover_of_isCoverDense
      (SmallEtale.topology B S hS Z'.1) U.unop, ?_⟩
  rintro W p ⟨⟨A, l, m, hfac⟩⟩
  have hA : (smallEtaleRingedToposHom B S hS i).fSharp.hom.app
        (op ((AffineEtale.inclusion B S hS Z'.1).obj A))
        ((smallEtaleRingedTopos B S hS Z').O.obj.map m.op a) = 0 :=
    (NatTrans.naturality_apply
      (smallEtaleRingedToposHom B S hS i).fSharp.hom m.op a).trans (by rw [ha, map_zero])
  have hnil : IsNilpotent ((smallEtaleRingedTopos B S hS Z').O.obj.map m.op a) :=
    isNilpotent_of_fSharp_app_eq_zero_of_isAffine B S hS i hci hsurj A.1 A.2 _ hA
  have hsplit : (smallEtaleRingedTopos B S hS Z').O.obj.map p.op a =
      (smallEtaleRingedTopos B S hS Z').O.obj.map l.op
        ((smallEtaleRingedTopos B S hS Z').O.obj.map m.op a) := by
    rw [← hfac, op_comp, Functor.map_comp, CategoryTheory.comp_apply]
  rw [hsplit]
  exact hnil.map ((smallEtaleRingedTopos B S hS Z').O.obj.map l.op).hom

/-! ### Surjectivity of the structure map -/

/-- **The structure map of the morphism of ringed topoi of a closed immersion is locally
surjective.** This is Stacks 03MB,
`AlgebraicGeometry.Space.isLocallySurjective_structureSharp`, read for the structure map of
sheaves of *commutative* rings carried by
`AlgebraicGeometry.Space.smallEtaleRingedToposHom`: the two have the same underlying map of
sheaves of sets by `AlgebraicGeometry.Space.forgetCommRingSheaf_map_fSharp`, and local
surjectivity depends on nothing else. -/
theorem isLocallySurjective_fSharp (i : Z ⟶ Z') (hci : IsClosedImmersion B S hS i.hom) :
    Presheaf.IsLocallySurjective (SmallEtale.topology B S hS Z'.1)
      (smallEtaleRingedToposHom B S hS i).fSharp.hom := by
  have h : Sheaf.IsLocallySurjective ((sheafCompose (SmallEtale.topology B S hS Z'.1)
      (forget₂ CommRingCat.{u} RingCat.{u})).map
        (smallEtaleRingedToposHom B S hS i).fSharp) := by
    rw [forgetCommRingSheaf_map_fSharp B S hS i]
    exact isLocallySurjective_structureSharp B S hS i hci
  exact ⟨fun s ↦ h.imageSieve_mem s⟩

end AlgebraicGeometry.Space

end
