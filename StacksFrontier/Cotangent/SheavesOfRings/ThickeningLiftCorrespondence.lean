module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.NaiveCotangentSixTermFirstTerms
public import StacksFrontier.AlgebraicGeometry.Scheme.NaiveCotangentImmersionDegreeZero
public import StacksFrontier.Cotangent.SheavesOfRings.RingedSpaceInverseImageExt
public import StacksFrontier.Cotangent.SheavesOfRings.ThickeningLocalHom
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.ClosedSubsetPullbackLeftExact
public import StacksFrontier.Topology.Sheaves.Functors.Pullback.UnitOnSections

/-!
# Morphisms of ringed spaces over a fixed continuous map, and the inverse image along a
homeomorphism

## Main definitions

* `AlgebraicGeometry.RingedSpace.homOverEquiv`: morphisms of ringed spaces `Z ⟶ W` lying over a
  given continuous map `β` are the morphisms `β⁻¹𝒪_W ⟶ 𝒪_Z` of sheaves of rings.
* `AlgebraicGeometry.Scheme.liftsEquivSheafHom`: for `i : X ⟶ X'` a homeomorphism on points
  (e.g. a thickening), `j : Y ⟶ Y'`, `f : X ⟶ Y` and `i ≫ pX' = f ≫ j ≫ pY'`, the morphisms of
  schemes `b : X' ⟶ Y'` over `T` with `i ≫ b = f ≫ j` are the maps
  `φ : f⁻¹𝒪_{Y'} ⟶ i⁻¹𝒪_{X'}` of sheaves of rings on `|X|` lying over `f` and under
  `(i ≫ pX')⁻¹𝒪_T`.
* `AlgebraicGeometry.Scheme.liftSourceReduction`: the reduction `f⁻¹𝒪_{Y'} ⟶ f⁻¹𝒪_Y`, with
  `liftSourceReduction_comp`.

## Main results

* `AlgebraicGeometry.RingedSpace.isIso_inverseImageProjection`: for a homeomorphism
  `i : Z ⟶ X`, the projection `(Z, i⁻¹𝒪_X) ⟶ (X, 𝒪_X)` is an isomorphism of ringed spaces.
* `AlgebraicGeometry.Scheme.isLocallySurjective_liftTargetReduction` and
  `AlgebraicGeometry.Scheme.isLocallySurjective_liftSourceReduction`: the two reductions
  `i⁻¹𝒪_{X'} ⟶ 𝒪_X` and `f⁻¹𝒪_{Y'} ⟶ f⁻¹𝒪_Y` are locally surjective when `i`, resp. `j`, is
  surjective on stalks (e.g. a closed immersion).
* `Stacks.Topology.isLocallySurjective_pullback_map`: the inverse image of a locally surjective
  map of sheaves of rings on a space is locally surjective.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace
open Stacks.SheafOfModules (ringedSpaceStructureMap)

universe u

namespace Stacks.Topology

variable {X Y : TopCat.{u}} (f : X ⟶ Y)

/-- The inverse image of a locally surjective map of sheaves of rings is locally surjective. -/
theorem isLocallySurjective_pullback_map {F G : TopCat.Sheaf CommRingCat.{u} Y} (φ : F ⟶ G)
    (hφ : TopCat.Presheaf.IsLocallySurjective φ.hom) :
    TopCat.Presheaf.IsLocallySurjective ((TopCat.Sheaf.pullback CommRingCat.{u} f).map φ).hom := by
  rw [TopCat.Presheaf.locally_surjective_iff_surjective_on_stalks] at hφ ⊢
  intro x t
  obtain ⟨U, hU, s, rfl⟩ := exists_ambientSection_germ f G x t
  obtain ⟨g, hg⟩ := hφ (f x) (G.presheaf.germ U (f x) hU s)
  obtain ⟨U', hU', s', rfl⟩ := F.presheaf.exists_germ_eq g
  have hx : x ∈ (Opens.map f).obj U' := hU'
  refine ⟨((TopCat.Sheaf.pullback CommRingCat.{u} f).obj F).presheaf.germ _ x hx
    (ambientSection f F (le_refl _) s'), ?_⟩
  rw [TopCat.Presheaf.stalkFunctor_map_germ_apply, ← hg,
    TopCat.Presheaf.stalkFunctor_map_germ_apply, ← germ_ambientSection f G (le_refl _) x hx,
    ambientSection_eq_unit, ambientSection_eq_unit]
  congr 1
  exact (ConcreteCategory.congr_hom (congrArg (fun t => t.hom.app (Opposite.op U'))
    ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} f).unit.naturality φ)) s').symm

end Stacks.Topology

namespace AlgebraicGeometry.RingedSpace

/-- The projection `(Z, i⁻¹𝒪_X) ⟶ (X, 𝒪_X)` is an isomorphism of ringed spaces when `i` is a
homeomorphism. -/
theorem isIso_inverseImageProjection (X : RingedSpace.{u, u}) {Z : TopCat.{u}}
    (i : Z ⟶ X.carrier) (hi : IsHomeomorph i) : IsIso (inverseImageProjection X i) := by
  have : SheafedSpace.IsOpenImmersion (inverseImageProjection X i) :=
    SheafedSpace.IsOpenImmersion.of_stalk_iso _ hi.isOpenEmbedding
      (H := isIso_stalkMap_inverseImageProjection X i)
  have : Epi (inverseImageProjection X i).hom.base :=
    (TopCat.epi_iff_surjective _).2 hi.surjective
  exact SheafedSpace.IsOpenImmersion.to_iso _

variable {Z W : RingedSpace.{u, u}}

/-- The morphism of ringed spaces over `β` with structure map adjoint to `φ : β⁻¹𝒪_W ⟶ 𝒪_Z`. -/
def homOver (β : Z.carrier ⟶ W.carrier)
    (φ : (TopCat.Sheaf.pullback CommRingCat.{u} β).obj W.sheaf ⟶ Z.sheaf) : Z ⟶ W :=
  InducedCategory.homMk
    { base := β
      c := (((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} β).homEquiv
        W.sheaf Z.sheaf) φ).hom }

/-- The base of `homOver β φ` is `β`. -/
@[simp]
theorem homOver_base (β : Z.carrier ⟶ W.carrier)
    (φ : (TopCat.Sheaf.pullback CommRingCat.{u} β).obj W.sheaf ⟶ Z.sheaf) :
    (homOver β φ).hom.base = β :=
  rfl

/-- The structure map of `homOver β φ` is `φ`. -/
@[simp]
theorem ringedSpaceStructureMap_homOver (β : Z.carrier ⟶ W.carrier)
    (φ : (TopCat.Sheaf.pullback CommRingCat.{u} β).obj W.sheaf ⟶ Z.sheaf) :
    ringedSpaceStructureMap (homOver β φ) = φ :=
  ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} β).homEquiv
    W.sheaf Z.sheaf).symm_apply_apply φ

/-- A morphism of ringed spaces over `β` is `homOver β` of its structure map. -/
theorem homOver_ringedSpaceStructureMap {β : Z.carrier ⟶ W.carrier} (χ : Z ⟶ W)
    (h : χ.hom.base = β) :
    homOver β (eqToHom (by rw [h]) ≫ ringedSpaceStructureMap χ) = χ := by
  subst h
  rw [eqToHom_refl, Category.id_comp]
  apply InducedCategory.hom_ext
  refine PresheafedSpace.hext _ _ rfl (heq_of_eq ?_)
  exact congrArg (fun t => t.hom) (((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u}
    χ.hom.base).homEquiv W.sheaf Z.sheaf).apply_symm_apply
      (⟨χ.hom.c⟩ : W.sheaf ⟶ (TopCat.Sheaf.pushforward CommRingCat.{u} χ.hom.base).obj Z.sheaf))

/-- A morphism of ringed spaces is `homOver` of its own base and structure map. -/
theorem homOver_base_ringedSpaceStructureMap (χ : Z ⟶ W) :
    homOver χ.hom.base (ringedSpaceStructureMap χ) = χ := by
  simpa using homOver_ringedSpaceStructureMap χ rfl

/-- Morphisms of ringed spaces `Z ⟶ W` over a fixed continuous map `β` are morphisms
`β⁻¹𝒪_W ⟶ 𝒪_Z` of sheaves of rings. -/
def homOverEquiv (β : Z.carrier ⟶ W.carrier) :
    { χ : Z ⟶ W // χ.hom.base = β } ≃
      ((TopCat.Sheaf.pullback CommRingCat.{u} β).obj W.sheaf ⟶ Z.sheaf) where
  toFun χ := eqToHom (by rw [χ.2]) ≫ ringedSpaceStructureMap χ.1
  invFun φ := ⟨homOver β φ, rfl⟩
  left_inv χ := Subtype.ext (homOver_ringedSpaceStructureMap χ.1 χ.2)
  right_inv φ := ringedSpaceStructureMap_homOver β φ

/-- Precomposing `homOver β φ` with the morphism `ι : (X, 𝒪_X) ⟶ (X, i⁻¹𝒪_{X'})` of the
inverse-image ringed space of a morphism `i : X ⟶ X'` postcomposes `φ` with the structure map
`i⁻¹𝒪_{X'} ⟶ 𝒪_X` of `i`. -/
theorem inverseImageSourceInclusion_comp_homOver {X X' : RingedSpace.{u, u}} (i : X ⟶ X')
    (β : X.carrier ⟶ W.carrier)
    (φ : (TopCat.Sheaf.pullback CommRingCat.{u} β).obj W.sheaf ⟶
      (inverseImage X' i.hom.base).sheaf) :
    inverseImageSourceInclusion i ≫ homOver (Z := inverseImage X' i.hom.base) β φ =
      homOver β (φ ≫ ringedSpaceStructureMap i) := by
  apply InducedCategory.hom_ext
  refine PresheafedSpace.hext _ _ rfl (heq_of_eq ?_)
  exact (congrArg (fun t => t.hom)
    (Adjunction.homEquiv_naturality_right
      (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} β) φ
      (ringedSpaceStructureMap i))).symm

/-- `homOver β` is injective. -/
theorem homOver_injective (β : Z.carrier ⟶ W.carrier) :
    Function.Injective (homOver (Z := Z) (W := W) β) := fun _ _ h =>
  (homOverEquiv β).symm.injective (Subtype.ext h)

/-- The structure map of `homOver β φ ≫ q` is `φ` precomposed with the inverse image along `β`
of the structure map of `q`, read through the comparison `(β ≫ q)⁻¹ ≅ β⁻¹ ∘ q⁻¹`. -/
theorem ringedSpaceStructureMap_homOver_comp {V : RingedSpace.{u, u}} (β : Z.carrier ⟶ W.carrier)
    (φ : (TopCat.Sheaf.pullback CommRingCat.{u} β).obj W.sheaf ⟶ Z.sheaf) (q : W ⟶ V) :
    ringedSpaceStructureMap (homOver β φ ≫ q) =
      (Stacks.SheafOfModules.inverseImageCompIso (homOver β φ) q).hom ≫
        (TopCat.Sheaf.pullback CommRingCat.{u} β).map (ringedSpaceStructureMap q) ≫ φ := by
  exact (Stacks.SheafOfModules.inverseImageCompIso_hom_comp (homOver β φ) q).symm.trans <|
    congrArg (fun t : (TopCat.Sheaf.pullback CommRingCat.{u} β).obj W.sheaf ⟶ Z.sheaf =>
    (Stacks.SheafOfModules.inverseImageCompIso (homOver β φ) q).hom ≫
      (TopCat.Sheaf.pullback CommRingCat.{u} β).map (ringedSpaceStructureMap q) ≫ t)
    (ringedSpaceStructureMap_homOver β φ)

end AlgebraicGeometry.RingedSpace

namespace AlgebraicGeometry.Scheme

open RingedSpace

variable {X X' Y Y' T : Scheme.{u}} (i : X ⟶ X') (j : Y ⟶ Y') (pX' : X' ⟶ T) (pY' : Y' ⟶ T)
  (f : X ⟶ Y)

/-- `(X, i⁻¹𝒪_{X'})`, the ringed space on `|X|` carrying `𝒪_{X'}` transported along `i`. -/
abbrev liftTargetSpace : RingedSpace.{u, u} :=
  inverseImage X'.toSheafedSpace i.toLRSHom.toShHom.hom.base

/-- The projection `(X, i⁻¹𝒪_{X'}) ⟶ X'`. -/
abbrev liftTargetProjection : liftTargetSpace i ⟶ X'.toSheafedSpace :=
  inverseImageProjection X'.toSheafedSpace i.toLRSHom.toShHom.hom.base

/-- The morphism `X ⟶ (X, i⁻¹𝒪_{X'})` through which `i` factors. -/
abbrev liftTargetInclusion : X.toSheafedSpace ⟶ liftTargetSpace i :=
  inverseImageSourceInclusion i.toLRSHom.toShHom

/-- `f⁻¹𝒪_{Y'}` on `|X|`: the inverse image of `𝒪_{Y'}` along `f ≫ j`. -/
abbrev liftSource : TopCat.Sheaf CommRingCat.{u} X.carrier :=
  (TopCat.Sheaf.pullback CommRingCat.{u} (f ≫ j).toLRSHom.toShHom.hom.base).obj Y'.sheaf

/-- `𝒪_{X'}` on `|X|`: the inverse image of `𝒪_{X'}` along `i`. -/
abbrev liftTarget : TopCat.Sheaf CommRingCat.{u} X.carrier :=
  (TopCat.Sheaf.pullback CommRingCat.{u} i.toLRSHom.toShHom.hom.base).obj X'.sheaf

/-- The inverse image `(i ≫ pX')⁻¹𝒪_T` of the structure sheaf of the base on `|X|`. -/
abbrev liftBase : TopCat.Sheaf CommRingCat.{u} X.carrier :=
  (TopCat.Sheaf.pullback CommRingCat.{u} (i ≫ pX').toLRSHom.toShHom.hom.base).obj T.sheaf

/-- The `𝒪_T`-algebra structure of `i⁻¹𝒪_{X'}`: the structure map of `(X, i⁻¹𝒪_{X'}) ⟶ X' ⟶ T`. -/
def liftTargetBaseMap : liftBase i pX' ⟶ liftTarget i :=
  ringedSpaceStructureMap (liftTargetProjection i ≫ pX'.toLRSHom.toShHom)

/-- The `𝒪_T`-algebra structure of `f⁻¹𝒪_{Y'}`, through `i ≫ pX' = f ≫ j ≫ pY'`: the comparison
`(f ≫ j ≫ pY')⁻¹ ≅ (f ≫ j)⁻¹ ∘ pY'⁻¹` followed by the inverse image of the structure map of
`pY'`. -/
def liftSourceBaseMap (hf : i ≫ pX' = f ≫ j ≫ pY') : liftBase i pX' ⟶ liftSource j f :=
  eqToHom (congrArg (fun t : X ⟶ T =>
      (TopCat.Sheaf.pullback CommRingCat.{u} t.toLRSHom.toShHom.hom.base).obj T.sheaf)
    (hf.trans (Category.assoc f j pY').symm)) ≫
    (Stacks.SheafOfModules.inverseImageCompIso (f ≫ j).toLRSHom.toShHom pY'.toLRSHom.toShHom).hom ≫
      (TopCat.Sheaf.pullback CommRingCat.{u} (f ≫ j).toLRSHom.toShHom.hom.base).map
        (ringedSpaceStructureMap pY'.toLRSHom.toShHom)

/-- Two morphisms of schemes with the same underlying morphism of sheafed spaces are equal. -/
theorem ext_of_toShHom {A B : Scheme.{u}} {a b : A ⟶ B}
    (h : a.toLRSHom.toShHom = b.toLRSHom.toShHom) : a = b :=
  Scheme.Hom.ext' (LocallyRingedSpace.Hom.ext' (congrArg (fun t => t.hom) h))

/-- `φ` lies over the structure map of `f ≫ j`, through the structure map of `i`, if and only if
the morphism of ringed spaces `(X, i⁻¹𝒪_{X'}) ⟶ Y'` it defines restricts along
`X ⟶ (X, i⁻¹𝒪_{X'})` to `f ≫ j`. -/
theorem liftCondOne_iff (φ : liftSource j f ⟶ liftTarget i) :
    φ ≫ ringedSpaceStructureMap i.toLRSHom.toShHom =
        ringedSpaceStructureMap (f ≫ j).toLRSHom.toShHom ↔
      liftTargetInclusion i ≫ homOver (Z := liftTargetSpace i)
          (f ≫ j).toLRSHom.toShHom.hom.base φ = (f ≫ j).toLRSHom.toShHom := by
  have e := inverseImageSourceInclusion_comp_homOver i.toLRSHom.toShHom
    (f ≫ j).toLRSHom.toShHom.hom.base φ
  exact ⟨fun h => e.trans ((congrArg (homOver (Z := X.toSheafedSpace)
      (f ≫ j).toLRSHom.toShHom.hom.base) h).trans (homOver_base_ringedSpaceStructureMap _)),
    fun h => homOver_injective _
      (e.symm.trans (h.trans (homOver_base_ringedSpaceStructureMap _).symm))⟩

/-- `φ` lies under `(i ≫ pX')⁻¹𝒪_T` if and only if the morphism of ringed spaces
`(X, i⁻¹𝒪_{X'}) ⟶ Y'` it defines, followed by `pY'`, is `(X, i⁻¹𝒪_{X'}) ⟶ X' ⟶ T`. -/
theorem liftCondTwo_iff (hf : i ≫ pX' = f ≫ j ≫ pY') (φ : liftSource j f ⟶ liftTarget i) :
    liftSourceBaseMap i j pX' pY' f hf ≫ φ = liftTargetBaseMap i pX' ↔
      homOver (Z := liftTargetSpace i) (f ≫ j).toLRSHom.toShHom.hom.base φ ≫
          pY'.toLRSHom.toShHom = liftTargetProjection i ≫ pX'.toLRSHom.toShHom := by
  have hk : (homOver (Z := liftTargetSpace i) (f ≫ j).toLRSHom.toShHom.hom.base φ ≫
      pY'.toLRSHom.toShHom).hom.base = (i ≫ pX').toLRSHom.toShHom.hom.base :=
    (congrArg (fun t : X ⟶ T => t.toLRSHom.toShHom.hom.base)
      (hf.trans (Category.assoc f j pY').symm)).symm
  have e1 : homOverEquiv (Z := liftTargetSpace i) (W := T.toSheafedSpace)
      (i ≫ pX').toLRSHom.toShHom.hom.base ⟨_, hk⟩ =
      liftSourceBaseMap i j pX' pY' f hf ≫ φ := by
    refine (congrArg (fun t => eqToHom _ ≫ t)
      (ringedSpaceStructureMap_homOver_comp (Z := liftTargetSpace i) _ φ
        pY'.toLRSHom.toShHom)).trans ?_
    simp only [liftSourceBaseMap, Category.assoc]
    rfl
  have e2 : homOverEquiv (Z := liftTargetSpace i) (W := T.toSheafedSpace)
      (i ≫ pX').toLRSHom.toShHom.hom.base
      ⟨liftTargetProjection i ≫ pX'.toLRSHom.toShHom, rfl⟩ = liftTargetBaseMap i pX' := by
    simp only [homOverEquiv]
    rfl
  exact ⟨fun h => congrArg Subtype.val ((homOverEquiv _).injective (e1.trans (h.trans e2.symm))),
    fun h => e1.symm.trans ((congrArg (homOverEquiv _) (Subtype.ext h)).trans e2)⟩

section Equiv

variable {i j pX' pY' f}

/-- The projection `(X, i⁻¹𝒪_{X'}) ⟶ X'` is an isomorphism when `i` is a homeomorphism. -/
private theorem isIso_liftTargetProjection (hi : IsHomeomorph i.base) :
    IsIso (liftTargetProjection i) :=
  isIso_inverseImageProjection X'.toSheafedSpace i.toLRSHom.toShHom.hom.base hi

/-- The map of sheaves of rings `f⁻¹𝒪_{Y'} ⟶ i⁻¹𝒪_{X'}` of a morphism `b : X' ⟶ Y'` with
`i ≫ b = f ≫ j`: the structure map of `(X, i⁻¹𝒪_{X'}) ⟶ X' ⟶ Y'`. -/
def liftToSheafHom (b : X' ⟶ Y') (hb : i ≫ b = f ≫ j) : liftSource j f ⟶ liftTarget i :=
  homOverEquiv (Z := liftTargetSpace i) (W := Y'.toSheafedSpace) _
    ⟨liftTargetProjection i ≫ b.toLRSHom.toShHom,
      congrArg (fun t : X ⟶ Y' => t.toLRSHom.toShHom.hom.base) hb⟩

/-- The morphism of ringed spaces defined by `liftToSheafHom b hb` is the composite
`(X, i⁻¹𝒪_{X'}) ⟶ X' ⟶ Y'`. -/
theorem homOver_liftToSheafHom (b : X' ⟶ Y') (hb : i ≫ b = f ≫ j) :
    homOver (Z := liftTargetSpace i) (f ≫ j).toLRSHom.toShHom.hom.base (liftToSheafHom b hb) =
      liftTargetProjection i ≫ b.toLRSHom.toShHom :=
  congrArg Subtype.val ((homOverEquiv _).symm_apply_apply _)

/-- The morphism of schemes `X' ⟶ Y'` of a map `φ : f⁻¹𝒪_{Y'} ⟶ i⁻¹𝒪_{X'}` lying over the
structure map of `f ≫ j`: the morphism of ringed spaces `X' ≅ (X, i⁻¹𝒪_{X'}) ⟶ Y'` defined by
`φ`. -/
def liftOfSheafHom (hi : IsHomeomorph i.base) (φ : liftSource j f ⟶ liftTarget i)
    (hφ : φ ≫ ringedSpaceStructureMap i.toLRSHom.toShHom =
      ringedSpaceStructureMap (f ≫ j).toLRSHom.toShHom) : X' ⟶ Y' :=
  haveI : IsIso (liftTargetProjection i) :=
    isIso_inverseImageProjection X'.toSheafedSpace i.toLRSHom.toShHom.hom.base hi
  have h : i.toLRSHom.toShHom ≫ (inv (liftTargetProjection i) ≫
      homOver (Z := liftTargetSpace i) (f ≫ j).toLRSHom.toShHom.hom.base φ) =
      (f ≫ j).toLRSHom.toShHom := by
    rw [← inverseImageSourceInclusion_comp_projection i.toLRSHom.toShHom, Category.assoc,
      IsIso.hom_inv_id_assoc]
    exact (liftCondOne_iff i j f φ).1 hφ
  homOfCompEq i j f
    (inv (liftTargetProjection i) ≫
      homOver (Z := liftTargetSpace i) (f ≫ j).toLRSHom.toShHom.hom.base φ)
    (congrArg (fun t : X.toSheafedSpace ⟶ Y'.toSheafedSpace => t.hom) h) hi.surjective

/-- The underlying morphism of `liftOfSheafHom hi φ hφ` is the inverse of the projection
`(X, i⁻¹𝒪_{X'}) ⟶ X'` followed by the morphism of ringed spaces defined by `φ`. -/
theorem liftOfSheafHom_toShHom (hi : IsHomeomorph i.base) (φ : liftSource j f ⟶ liftTarget i)
    (hφ : φ ≫ ringedSpaceStructureMap i.toLRSHom.toShHom =
      ringedSpaceStructureMap (f ≫ j).toLRSHom.toShHom) :
    haveI : IsIso (liftTargetProjection i) :=
      isIso_inverseImageProjection X'.toSheafedSpace i.toLRSHom.toShHom.hom.base hi
    (liftOfSheafHom hi φ hφ).toLRSHom.toShHom =
      inv (liftTargetProjection i) ≫
        homOver (Z := liftTargetSpace i) (f ≫ j).toLRSHom.toShHom.hom.base φ :=
  rfl

/-- The projection `(X, i⁻¹𝒪_{X'}) ⟶ X'` followed by `liftOfSheafHom hi φ hφ` is the morphism of
ringed spaces defined by `φ`. -/
theorem liftTargetProjection_comp_liftOfSheafHom (hi : IsHomeomorph i.base)
    (φ : liftSource j f ⟶ liftTarget i)
    (hφ : φ ≫ ringedSpaceStructureMap i.toLRSHom.toShHom =
      ringedSpaceStructureMap (f ≫ j).toLRSHom.toShHom) :
    liftTargetProjection i ≫ (liftOfSheafHom hi φ hφ).toLRSHom.toShHom =
      homOver (Z := liftTargetSpace i) (f ≫ j).toLRSHom.toShHom.hom.base φ := by
  have := isIso_liftTargetProjection hi
  rw [liftOfSheafHom_toShHom, IsIso.hom_inv_id_assoc]

/-- The map `liftToSheafHom b hb` lies over the structure map of `f ≫ j`: followed by the
structure map `i⁻¹𝒪_{X'} ⟶ 𝒪_X` of `i` it is the structure map of `f ≫ j`. -/
theorem liftToSheafHom_condOne (b : X' ⟶ Y') (hb : i ≫ b = f ≫ j) :
    liftToSheafHom b hb ≫ ringedSpaceStructureMap i.toLRSHom.toShHom =
      ringedSpaceStructureMap (f ≫ j).toLRSHom.toShHom :=
  (liftCondOne_iff i j f _).2 ((congrArg (liftTargetInclusion i ≫ ·)
    (homOver_liftToSheafHom b hb)).trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ b.toLRSHom.toShHom)
        (inverseImageSourceInclusion_comp_projection i.toLRSHom.toShHom)).trans
        (congrArg (fun t : X ⟶ Y' => t.toLRSHom.toShHom) hb))))

/-- The morphism `liftOfSheafHom hi φ hφ` extends `f ≫ j` along `i`. -/
theorem comp_liftOfSheafHom (hi : IsHomeomorph i.base) (φ : liftSource j f ⟶ liftTarget i)
    (hφ : φ ≫ ringedSpaceStructureMap i.toLRSHom.toShHom =
      ringedSpaceStructureMap (f ≫ j).toLRSHom.toShHom) :
    i ≫ liftOfSheafHom hi φ hφ = f ≫ j :=
  ext_of_toShHom ((congrArg (fun t => t ≫ (liftOfSheafHom hi φ hφ).toLRSHom.toShHom)
    (inverseImageSourceInclusion_comp_projection i.toLRSHom.toShHom).symm).trans
    ((Category.assoc _ _ _).trans
      ((congrArg (liftTargetInclusion i ≫ ·)
        (liftTargetProjection_comp_liftOfSheafHom hi φ hφ)).trans
        ((liftCondOne_iff i j f φ).1 hφ))))

/-- When `φ` lies under `(i ≫ pX')⁻¹𝒪_T`, the morphism `liftOfSheafHom hi φ hφ` is a morphism
over `T`. -/
theorem liftOfSheafHom_comp_base (hf : i ≫ pX' = f ≫ j ≫ pY') (hi : IsHomeomorph i.base)
    (φ : liftSource j f ⟶ liftTarget i)
    (hφ : φ ≫ ringedSpaceStructureMap i.toLRSHom.toShHom =
      ringedSpaceStructureMap (f ≫ j).toLRSHom.toShHom)
    (h2 : liftSourceBaseMap i j pX' pY' f hf ≫ φ = liftTargetBaseMap i pX') :
    liftOfSheafHom hi φ hφ ≫ pY' = pX' := by
  have := isIso_liftTargetProjection hi
  exact ext_of_toShHom ((cancel_epi (liftTargetProjection i)).1 ((Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ pY'.toLRSHom.toShHom)
      (liftTargetProjection_comp_liftOfSheafHom hi φ hφ)).trans
      ((liftCondTwo_iff i j pX' pY' f hf φ).1 h2))))

end Equiv

/-- Let `i : X ⟶ X'` be a morphism of schemes which is a homeomorphism on points (for instance a
thickening), let `j : Y ⟶ Y'`, `pX' : X' ⟶ T`, `pY' : Y' ⟶ T` and `f : X ⟶ Y` with
`i ≫ pX' = f ≫ j ≫ pY'`.  The morphisms of schemes `b : X' ⟶ Y'` over `T` with `i ≫ b = f ≫ j`
are the morphisms `φ : f⁻¹𝒪_{Y'} ⟶ i⁻¹𝒪_{X'}` of sheaves of rings on `|X|` which lie over the
structure map `(f ≫ j)⁻¹𝒪_{Y'} ⟶ 𝒪_X` (through the structure map `i⁻¹𝒪_{X'} ⟶ 𝒪_X` of `i`) and
under `(i ≫ pX')⁻¹𝒪_T`. -/
def liftsEquivSheafHom (hi : IsHomeomorph i.base) (hf : i ≫ pX' = f ≫ j ≫ pY') :
    { b : X' ⟶ Y' // b ≫ pY' = pX' ∧ i ≫ b = f ≫ j } ≃
      { φ : liftSource j f ⟶ liftTarget i //
          φ ≫ ringedSpaceStructureMap i.toLRSHom.toShHom =
            ringedSpaceStructureMap (f ≫ j).toLRSHom.toShHom ∧
          liftSourceBaseMap i j pX' pY' f hf ≫ φ = liftTargetBaseMap i pX' } where
  toFun b :=
    ⟨liftToSheafHom b.1 b.2.2, liftToSheafHom_condOne b.1 b.2.2,
      (liftCondTwo_iff i j pX' pY' f hf _).2 ((congrArg (· ≫ pY'.toLRSHom.toShHom)
        (homOver_liftToSheafHom b.1 b.2.2)).trans ((Category.assoc _ _ _).trans
          (congrArg (fun t : X' ⟶ T => liftTargetProjection i ≫ t.toLRSHom.toShHom) b.2.1)))⟩
  invFun φ :=
    ⟨liftOfSheafHom hi φ.1 φ.2.1, liftOfSheafHom_comp_base hf hi φ.1 φ.2.1 φ.2.2,
      comp_liftOfSheafHom hi φ.1 φ.2.1⟩
  left_inv b := by
    have : IsIso (liftTargetProjection i) :=
      isIso_inverseImageProjection X'.toSheafedSpace i.toLRSHom.toShHom.hom.base hi
    exact Subtype.ext (ext_of_toShHom ((cancel_epi (liftTargetProjection i)).1
      ((liftTargetProjection_comp_liftOfSheafHom hi (liftToSheafHom b.1 b.2.2)
        (liftToSheafHom_condOne b.1 b.2.2)).trans (homOver_liftToSheafHom b.1 b.2.2))))
  right_inv φ := Subtype.ext (homOver_injective (Z := liftTargetSpace i) (W := Y'.toSheafedSpace)
    (f ≫ j).toLRSHom.toShHom.hom.base
    ((homOver_liftToSheafHom (liftOfSheafHom hi φ.1 φ.2.1) (comp_liftOfSheafHom hi φ.1 φ.2.1)).trans
      (liftTargetProjection_comp_liftOfSheafHom hi φ.1 φ.2.1)))

/-! ### The two reductions -/

/-- The reduction `f⁻¹𝒪_{Y'} ⟶ f⁻¹𝒪_Y` of the source: the inverse image along `f` of the
structure map `j⁻¹𝒪_{Y'} ⟶ 𝒪_Y` of `j`, read through `(f ≫ j)⁻¹ ≅ f⁻¹ ∘ j⁻¹`. -/
def liftSourceReduction :
    liftSource j f ⟶
      (TopCat.Sheaf.pullback CommRingCat.{u} f.toLRSHom.toShHom.hom.base).obj Y.sheaf :=
  (Stacks.SheafOfModules.inverseImageCompIso f.toLRSHom.toShHom j.toLRSHom.toShHom).hom ≫
    Stacks.SheafOfModules.inverseImageFirstRingMap f.toLRSHom.toShHom j.toLRSHom.toShHom

/-- The reduction of the source followed by `f♯ : f⁻¹𝒪_Y ⟶ 𝒪_X` is the structure map of
`f ≫ j`. -/
theorem liftSourceReduction_comp :
    liftSourceReduction j f ≫ ringedSpaceStructureMap f.toLRSHom.toShHom =
      ringedSpaceStructureMap (f ≫ j).toLRSHom.toShHom :=
  (Category.assoc _ _ _).trans
    (Stacks.SheafOfModules.inverseImageCompIso_hom_comp f.toLRSHom.toShHom j.toLRSHom.toShHom)

/-- The structure map `i⁻¹𝒪_{X'} ⟶ 𝒪_X` of a morphism surjective on stalks (for instance a
closed immersion) is locally surjective. -/
theorem isLocallySurjective_liftTargetReduction [SurjectiveOnStalks i] :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology X.carrier)
      (ringedSpaceStructureMap i.toLRSHom.toShHom).hom :=
  Stacks.NaiveCotangentDegreeZero.isLocallySurjective_inverseImageStructureMap i

/-- The reduction `f⁻¹𝒪_{Y'} ⟶ f⁻¹𝒪_Y` of the source is locally surjective when `j` is surjective
on stalks (for instance a closed immersion). -/
theorem isLocallySurjective_liftSourceReduction [SurjectiveOnStalks j] :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology X.carrier)
      (liftSourceReduction j f).hom := by
  have hj := isLocallySurjective_liftTargetReduction j
  have : Presheaf.IsLocallySurjective (Opens.grothendieckTopology X.carrier)
      (Stacks.SheafOfModules.inverseImageFirstRingMap f.toLRSHom.toShHom
        j.toLRSHom.toShHom).hom :=
    Stacks.Topology.isLocallySurjective_pullback_map _ _ hj
  have : IsIso (Stacks.SheafOfModules.inverseImageCompIso f.toLRSHom.toShHom
      j.toLRSHom.toShHom).hom.hom :=
    ((sheafToPresheaf _ _).mapIso (Stacks.SheafOfModules.inverseImageCompIso
      f.toLRSHom.toShHom j.toLRSHom.toShHom)).isIso_hom
  exact Presheaf.isLocallySurjective_comp (J := Opens.grothendieckTopology X.carrier)
    (Stacks.SheafOfModules.inverseImageCompIso f.toLRSHom.toShHom j.toLRSHom.toShHom).hom.hom
    (Stacks.SheafOfModules.inverseImageFirstRingMap f.toLRSHom.toShHom j.toLRSHom.toShHom).hom

end AlgebraicGeometry.Scheme

end
