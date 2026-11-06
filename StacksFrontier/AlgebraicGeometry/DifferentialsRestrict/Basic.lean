module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import StacksFrontier.AlgebraicGeometry.Topologies.InverseImageStructureSheaf
public import Mathlib.AlgebraicGeometry.Restrict
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.Functoriality
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialsPresheafFunctorial

/-!
# Restriction of the sheaf of relative differentials

Let `f : X ⟶ S` be a morphism of schemes, let `V` be an open of `S` and let `U ≤ f ⁻¹ᵁ V` be an
open of `X`, so that `f` restricts to a morphism `U ⟶ V`. This file proves that the restriction
to `U` of the sheaf of relative differentials of `f` is the sheaf of relative differentials of
that restricted morphism, by the unique isomorphism carrying the restricted universal derivation
to the universal derivation.

## Main definitions

* `restrictedDerivation` is the universal relative derivation of `f`, read on the opens of `U` as
  a derivation relative to the structural map of the restricted morphism.
* `basePullbackComparison` compares the inverse image of the structure sheaf of `V` along the
  restricted morphism with the restriction to `U` of the inverse image of the structure sheaf of
  `S`.
* `fromRestrict` and `toRestrict` are the two comparison morphisms, and `restrictIso` is the
  isomorphism they form.

## Main results

* `structuralMap_comp_restrictStructureMap`: the structural map of the restricted morphism
  factors through the restriction of the structural map of `f`, along
  `basePullbackComparison`.
* `toRestrict_d`: the comparison morphism carries universal relative differentials of `f` to
  universal relative differentials of the restricted morphism.
* `hom_ext_of_postcomp`: a morphism out of the restriction of the relative differentials is
  determined by its effect on the restricted derivation.
* `existsUnique_relativeDifferentials_restrict` is the unique-existence statement.

## Implementation notes

The whole content is the vanishing condition. A relative derivation of `f` is by definition a
derivation relative to the structural map `f⁻¹ 𝒪_S ⟶ 𝒪_X`, so to read it on `U` as a derivation
for the restricted morphism one has to know that it annihilates the image of the sections of
`(f.resLE V U e)⁻¹ 𝒪_V`. The sections of an inverse image sheaf are a sheafified colimit and so
are not computable, and the two inverse image sheaves here are formed along different maps; what
replaces a computation is `basePullbackComparison`, a morphism between them, because a vanishing
condition transports along a morphism of sheaves of rings. That morphism is obtained by
transposing across the very adjunction that defines inverse images, so no sheafification is
touched: its transpose `baseComparison` sends a section of `𝒪_S` over `V.ι ''ᵁ W` to its
inverse-image section, restricted to the image of the preimage of `W`, and the square that has to
commute does so because both of its transposes are the single restriction map
`f.appLE (V.ι ''ᵁ W) (U.ι ''ᵁ _)`. With the comparison in hand the derivation itself is the
composite-derivation construction for a commutative square of sheaves of commutative rings, whose
restriction of scalars is exactly the restriction functor on modules along an open immersion.

The two comparison morphisms then come from different places. `fromRestrict` is the universal
property of the relative differentials of the restricted morphism, applied to the restricted
derivation. `toRestrict` is the canonical morphism of relative differentials of the commutative
square formed by `f`, its restriction and the two inclusions, read through the identification of
restriction with pullback; those two functors are both left adjoint to pushforward, so the
canonical morphism and `toRestrict` have the same transpose, which is what makes the
characterization of the canonical morphism usable on sections of the restriction.

Only one of the two composites needs the universal property of the relative differentials of the
restricted morphism; the other needs that a morphism out of the restriction is determined by the
restricted derivation. That second fact is proved by transposing and appealing to the universal
property of the relative differentials of `f` itself, which is why no comparison of inverse image
sheaves in the opposite direction is required. Both composites are then identities as soon as
`toRestrict` carries the restricted derivation to the universal derivation, and that single
computation is `toRestrict_d`.

`toRestrict_d` is first proved for an open of `U` presented as `U.ι ⁻¹ᵁ (U.ι ''ᵁ W)`, since that
is where the unit of the restriction adjunction lands, and the section fed to the characterization
is the preimage of the given one under the section isomorphism of the open immersion, which is an
isomorphism on an image open. The statement is then moved to an arbitrary open by rewriting with
`Scheme.Hom.preimage_image_eq`, a rewrite that is well behaved because the open occurs uniformly
in the type of the section and in both sides.

Everything is in a single universe. The schemes are in `Scheme.{u}` and `X.Modules` is
`SheafOfModules.{u} X.ringCatSheaf`, so the three universe parameters of the sheaf-theoretic
module of relative differentials are all `u` and no universe side condition arises; this also
meets the requirement of the inverse image constructions that space, rings and modules lie in one
universe.

Two transparency points. `TopCat.Sheaf` and `AlgebraicGeometry.Scheme.Modules`
are definitions, so a goal mentioning the underlying presheaf of a sheaf of rings or of modules is
not type-correct at implicit transparency and `rw` and `simp` fail to find patterns that the goal
plainly displays; the naturality of `baseComparison`, the factorization of the structural map and
the uniqueness arguments are therefore written in term mode out of `congrArg`, `Eq.trans` and
explicit instances of `Functor.map_comp`, which need only default transparency. Relatedly, after
rewriting with `Scheme.Opens.ι_appIso` the resulting identity morphism carries the ambient
spelling of its object, so `Category.comp_id` cannot be rewritten and has to be applied as a term.

## What is not done here

Stacks 01UT is not closed by this. Transporting the comparison of
`Stacks.AlgebraicGeometry.AffineDifferentials.kaehlerToSections` along this isomorphism reduces
01UT for the pair `(V, U)` to the same assertion for the restricted morphism on global sections,
which is the case of two affine schemes; that case still requires a relative derivation to be
constructed out of ring data, which is the global-sections form of Stacks 01UO, and that is
absent from this library. That reduction is not carried out here either. The sections form of the
isomorphism is not extracted, and the isomorphism is not shown to be natural in `U` and `V` or
compatible with composition of morphisms. No tag attribute is attached to any declaration here.

## References

* [Stacks Project, Tag 01US](https://stacks.math.columbia.edu/tag/01US)
* [Stacks Project, Tag 01UV](https://stacks.math.columbia.edu/tag/01UV)
* [Stacks Project, Tag 08RM](https://stacks.math.columbia.edu/tag/08RM)
* [Stacks Project, Tag 08RS](https://stacks.math.columbia.edu/tag/08RS)
* [Stacks Project, Tag 01SA](https://stacks.math.columbia.edu/tag/01SA)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

universe u

namespace Stacks.AlgebraicGeometry.DifferentialsRestrict

variable {X S : Scheme.{u}} (f : X ⟶ S) (V : S.Opens) (U : X.Opens) (e : U ≤ f ⁻¹ᵁ V)

/-- Restriction of sheaves of commutative rings along the inclusion of an open. -/
noncomputable abbrev restrictRingSheaf :
    TopCat.Sheaf CommRingCat.{u} X ⥤ TopCat.Sheaf CommRingCat.{u} U.toScheme :=
  U.ι.opensFunctor.sheafPushforwardContinuous CommRingCat.{u}
    (Opens.grothendieckTopology U.toScheme) (Opens.grothendieckTopology X)

/-- The comparison identifying the structure sheaf of `U` with the restriction of the
structure sheaf of `X`, on underlying presheaves. -/
noncomputable def restrictStructureMap :
    U.toScheme.presheaf ⟶ U.ι.opensFunctor.op ⋙ X.presheaf where
  app W := (U.ι.appIso W.unop).inv

/-- The comparison identifying the structure sheaf of `U` with the restriction of the
structure sheaf of `X`. -/
noncomputable def restrictStructureMapSheaf :
    U.toScheme.sheaf ⟶ (restrictRingSheaf U).obj X.sheaf where
  hom := restrictStructureMap U

/-- The unit of the inverse-image/pushforward adjunction at the structure sheaf of the base. -/
noncomputable abbrev baseUnit := ((TopCat.Sheaf.pullbackPushforwardAdjunction
  CommRingCat.{u} f.base).unit.app S.sheaf).hom

/-- The restriction of the structural map of `f` to the open `U`. -/
noncomputable abbrev restrictedStructuralMap :=
  ((restrictRingSheaf U).map (inverseImageStructureMap f)).hom

/-- The image of an open of `U` over an open of `V` lies in the preimage of its image. -/
theorem image_resLE_preimage_le (W : V.toScheme.Opens) :
    U.ι ''ᵁ (f.resLE V U e) ⁻¹ᵁ W ≤ f ⁻¹ᵁ (V.ι ''ᵁ W) :=
  (Scheme.Hom.le_resLE_preimage_iff f e W _).mp le_rfl

/-- The comparison from the structure sheaf of `V` to the pushforward along the restricted
morphism of the restriction to `U` of the inverse image of the structure sheaf of `S`: take
the inverse-image section of a section of `𝒪_S` and restrict it. -/
noncomputable def baseComparison :
    V.toScheme.sheaf ⟶ (TopCat.Sheaf.pushforward CommRingCat.{u}
      (f.resLE V U e).base).obj ((restrictRingSheaf U).obj (f.inverseImageStructureSheaf)) where
  hom :=
  { app W := (baseUnit f).app (op (V.ι ''ᵁ W.unop)) ≫
      (f.inverseImageStructureSheaf).presheaf.map
        (homOfLE (image_resLE_preimage_le f V U e W.unop)).op
    naturality := by
      intro W W' g
      refine (Category.assoc _ _ _).symm.trans ?_
      refine (congrArg (fun t => t ≫ (f.inverseImageStructureSheaf).presheaf.map
        (homOfLE (image_resLE_preimage_le f V U e W'.unop)).op)
        ((baseUnit f).naturality (V.ι.opensFunctor.op.map g))).trans ?_
      refine (Category.assoc _ _ _).trans ?_
      refine Eq.trans ?_ (Category.assoc _ _ _).symm
      refine congrArg (fun t => (baseUnit f).app (op (V.ι ''ᵁ W.unop)) ≫ t) ?_
      exact (((f.inverseImageStructureSheaf).presheaf.map_comp
          ((Opens.map f.base).op.map (V.ι.opensFunctor.op.map g))
          (homOfLE (image_resLE_preimage_le f V U e W'.unop)).op).symm.trans
        ((f.inverseImageStructureSheaf).presheaf.map_comp
          (homOfLE (image_resLE_preimage_le f V U e W.unop)).op
          (U.ι.opensFunctor.op.map ((Opens.map (f.resLE V U e).base).op.map g)))) }

/-- The comparison from the inverse image along the restricted morphism of the structure
sheaf of `V` to the restriction to `U` of the inverse image of the structure sheaf of `S`. -/
noncomputable def basePullbackComparison :
    (TopCat.Sheaf.pullback CommRingCat.{u} (f.resLE V U e).base).obj V.toScheme.sheaf ⟶
      (restrictRingSheaf U).obj (f.inverseImageStructureSheaf) :=
  ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} (f.resLE V U e).base).homEquiv
    V.toScheme.sheaf ((restrictRingSheaf U).obj (f.inverseImageStructureSheaf))).symm
      (baseComparison f V U e)

/-- The comorphism of `f` on an open of the base is the inverse-image section map followed by
the structural map, which is how the structural map is defined. -/
theorem comorphism_eq_baseUnit_comp (A : (Opens S)ᵒᵖ) :
    f.c.app A = (baseUnit f).app A ≫
      (inverseImageStructureMap f).hom.app ((Opens.map f.base).op.obj A) := by
  let adj := TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} f.base
  let fc : S.sheaf ⟶ (TopCat.Sheaf.pushforward CommRingCat.{u} f.base).obj X.sheaf := ⟨f.c⟩
  have hfc : adj.homEquiv S.sheaf X.sheaf (inverseImageStructureMap f) = fc :=
    (adj.homEquiv S.sheaf X.sheaf).apply_symm_apply fc
  have hunit := adj.homEquiv_unit S.sheaf X.sheaf (inverseImageStructureMap f)
  rw [hfc] at hunit
  exact congrArg (fun g => g.hom.app A) hunit

/-- On an open of `V`, the comorphism of the restricted morphism followed by the comparison of
structure sheaves is the restriction map of `f` between the corresponding opens. -/
theorem resLE_app_comp_appIso_inv (W : V.toScheme.Opens) :
    (f.resLE V U e).app W ≫ (U.ι.appIso ((f.resLE V U e) ⁻¹ᵁ W)).inv =
      f.appLE (V.ι ''ᵁ W) (U.ι ''ᵁ (f.resLE V U e) ⁻¹ᵁ W)
        (image_resLE_preimage_le f V U e W) := by
  rw [Scheme.Opens.ι_appIso, Iso.refl_inv]
  exact (Category.comp_id _).trans
    ((Scheme.Hom.app_eq_appLE _).trans (Scheme.Hom.resLE_appLE f e _ _ le_rfl))

/-- On an open of `V`, the base comparison followed by the restricted structural map is the
restriction map of `f` between the corresponding opens. -/
theorem baseComparison_app_comp_restrictedStructuralMap (W : (Opens V.toScheme)ᵒᵖ) :
    (baseComparison f V U e).hom.app W ≫
        (restrictedStructuralMap f U).app ((Opens.map (f.resLE V U e).base).op.obj W) =
      f.appLE (V.ι ''ᵁ W.unop) (U.ι ''ᵁ (f.resLE V U e) ⁻¹ᵁ W.unop)
        (image_resLE_preimage_le f V U e W.unop) :=
  (Category.assoc _ _ _).trans
    ((congrArg (fun t => (baseUnit f).app (op (V.ι ''ᵁ W.unop)) ≫ t)
        ((inverseImageStructureMap f).hom.naturality
          (homOfLE (image_resLE_preimage_le f V U e W.unop)).op)).trans
      ((Category.assoc _ _ _).symm.trans
        (congrArg
          (fun t => t ≫ X.presheaf.map
            (homOfLE (image_resLE_preimage_le f V U e W.unop)).op)
          (comorphism_eq_baseUnit_comp f (op (V.ι ''ᵁ W.unop))).symm)))

/-- The structural map of the restricted morphism, followed by the comparison of structure
sheaves, factors through the restricted structural map of `f`. -/
theorem structuralMap_comp_restrictStructureMapSheaf :
    inverseImageStructureMap (f.resLE V U e) ≫ restrictStructureMapSheaf U =
      basePullbackComparison f V U e ≫
        (restrictRingSheaf U).map (inverseImageStructureMap f) := by
  let adj := TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} (f.resLE V U e).base
  let fc : V.toScheme.sheaf ⟶ (TopCat.Sheaf.pushforward CommRingCat.{u}
    (f.resLE V U e).base).obj U.toScheme.sheaf := ⟨(f.resLE V U e).c⟩
  have h1 := adj.homEquiv_naturality_right (inverseImageStructureMap (f.resLE V U e))
    (restrictStructureMapSheaf U)
  have h2 := adj.homEquiv_naturality_right (basePullbackComparison f V U e)
    ((restrictRingSheaf U).map (inverseImageStructureMap f))
  have h3 : adj.homEquiv V.toScheme.sheaf U.toScheme.sheaf
      (inverseImageStructureMap (f.resLE V U e)) = fc :=
    (adj.homEquiv V.toScheme.sheaf U.toScheme.sheaf).apply_symm_apply fc
  have h4 : adj.homEquiv V.toScheme.sheaf ((restrictRingSheaf U).obj (f.inverseImageStructureSheaf))
      (basePullbackComparison f V U e) = baseComparison f V U e :=
    (adj.homEquiv V.toScheme.sheaf _).apply_symm_apply (baseComparison f V U e)
  refine (adj.homEquiv V.toScheme.sheaf ((restrictRingSheaf U).obj X.sheaf)).injective
    (h1.trans (Eq.trans ?_ h2.symm))
  refine (congrArg (fun t => t ≫ (TopCat.Sheaf.pushforward CommRingCat.{u}
    (f.resLE V U e).base).map (restrictStructureMapSheaf U)) h3).trans ?_
  refine Eq.trans ?_ (congrArg (fun t => t ≫ (TopCat.Sheaf.pushforward CommRingCat.{u}
    (f.resLE V U e).base).map ((restrictRingSheaf U).map (inverseImageStructureMap f))) h4).symm
  refine ObjectProperty.hom_ext _ (NatTrans.ext (funext fun W => ?_))
  exact (resLE_app_comp_appIso_inv f V U e W.unop).trans
    (baseComparison_app_comp_restrictedStructuralMap f V U e W).symm

/-- The presheaf form of the factorization of the restricted structural map. -/
theorem structuralMap_comp_restrictStructureMap :
    (inverseImageStructureMap (f.resLE V U e)).hom ≫ restrictStructureMap U =
      (basePullbackComparison f V U e).hom ≫ restrictedStructuralMap f U :=
  congrArg (fun m => m.hom) (structuralMap_comp_restrictStructureMapSheaf f V U e)

/-- The universal relative derivation of `f`, read on the opens of `X` that are images of
opens of `U`. -/
noncomputable def pushedDerivation :
    PresheafOfModulesOfCommRing.Derivation
      ((PresheafOfModules.pushforward₀OfCommRingCat U.ι.opensFunctor X.presheaf).obj
        (Scheme.Hom.relativeDifferentials f).val)
      (F := 𝟭 (Opens U.toScheme)) (restrictedStructuralMap f U) where
  d {W} := (Scheme.Hom.universalRelativeDerivation f).d (X := U.ι.opensFunctor.op.obj W)
  d_mul := fun {W} a b => (Scheme.Hom.universalRelativeDerivation f).d_mul
    (X := U.ι.opensFunctor.op.obj W) a b
  d_map := fun {_ _} g a => (Scheme.Hom.universalRelativeDerivation f).d_map
    (U.ι.opensFunctor.op.map g) a
  d_app := fun {W} a => (Scheme.Hom.universalRelativeDerivation f).d_app
    (X := U.ι.opensFunctor.op.obj W) a

/-- The restriction to `U` of the universal relative derivation of `f`, as a derivation
relative to the structural map of the restricted morphism. -/
noncomputable def restrictedDerivation :
    SheafOfModules.SheafDerivation (inverseImageStructureMap (f.resLE V U e))
      (Scheme.Modules.restrict (Scheme.Hom.relativeDifferentials f) U.ι) := by
  change PresheafOfModulesOfCommRing.Derivation'
    ((PresheafOfModules.restrictScalars (Functor.whiskerRight (restrictStructureMap U)
    (forget₂ CommRingCat RingCat))).obj
      ((PresheafOfModules.pushforward₀OfCommRingCat U.ι.opensFunctor X.presheaf).obj
        (Scheme.Hom.relativeDifferentials f).val))
          (inverseImageStructureMap (f.resLE V U e)).hom
  exact SheafDifferentials.compDeriv (pushedDerivation f U) (restrictStructureMap U)
    (basePullbackComparison f V U e).hom (structuralMap_comp_restrictStructureMap f V U e)

/-- The restricted derivation sends a section of the structure sheaf of `U` to the universal
relative differential of the corresponding section of the structure sheaf of `X`. -/
theorem restrictedDerivation_d (W : U.toScheme.Opens) (x : Γ(U.toScheme, W)) :
    (restrictedDerivation f V U e).d (X := op W) x =
      (Scheme.Hom.universalRelativeDerivation f).d (((U.ι.appIso W).inv).hom x) :=
  rfl

/-! ### The two comparison morphisms -/

/-- The morphism from the relative differentials of the restricted morphism to the
restriction of the relative differentials, induced by the restricted derivation. -/
noncomputable def fromRestrict :
    Scheme.Hom.relativeDifferentials (f.resLE V U e) ⟶
      Scheme.Modules.restrict (Scheme.Hom.relativeDifferentials f) U.ι :=
  Classical.choose (SheafOfModules.universalDerivation_isUniversal
    (inverseImageStructureMap (f.resLE V U e)) _ (restrictedDerivation f V U e))

/-- `fromRestrict` carries the universal derivation of the restricted morphism to the
restricted derivation. -/
theorem fromRestrict_spec :
    (Scheme.Hom.universalRelativeDerivation (f.resLE V U e)).postcomp
        (fromRestrict f V U e).val = restrictedDerivation f V U e :=
  (Classical.choose_spec (SheafOfModules.universalDerivation_isUniversal
    (inverseImageStructureMap (f.resLE V U e)) _ (restrictedDerivation f V U e))).1

/-- `fromRestrict` sends the universal differential of a section of the structure sheaf of
`U` to the universal relative differential of the corresponding section on `X`. -/
theorem fromRestrict_d (W : U.toScheme.Opens) (x : Γ(U.toScheme, W)) :
    ((fromRestrict f V U e).val.app (op W)).hom
        ((Scheme.Hom.universalRelativeDerivation (f.resLE V U e)).d x) =
      (Scheme.Hom.universalRelativeDerivation f).d (((U.ι.appIso W).inv).hom x) :=
  PresheafOfModulesOfCommRing.Derivation.congr_d (fromRestrict_spec f V U e) x

/-- The commutative square formed by `f`, its restriction and the two inclusions. -/
theorem resLE_square : U.ι ≫ f = f.resLE V U e ≫ V.ι :=
  (Scheme.Hom.resLE_comp_ι f e).symm

/-- The morphism from the restriction of the relative differentials to the relative
differentials of the restricted morphism: the canonical morphism of relative differentials
of the commutative square, read through the identification of restriction with pullback. -/
noncomputable def toRestrict :
    Scheme.Modules.restrict (Scheme.Hom.relativeDifferentials f) U.ι ⟶
      Scheme.Hom.relativeDifferentials (f.resLE V U e) :=
  (Scheme.Modules.restrictFunctorIsoPullback U.ι).hom.app
      (Scheme.Hom.relativeDifferentials f) ≫
    Scheme.Hom.relativeDifferentialsMap U.ι f (f.resLE V U e) V.ι (resLE_square f V U e)

/-- Under the restriction/pushforward adjunction, `toRestrict` has the same transpose as the
canonical morphism of the square has under the pullback/pushforward adjunction. -/
theorem restrictAdjunction_homEquiv_toRestrict :
    (Scheme.Modules.restrictAdjunction U.ι).homEquiv (Scheme.Hom.relativeDifferentials f)
        (Scheme.Hom.relativeDifferentials (f.resLE V U e)) (toRestrict f V U e) =
      (Scheme.Modules.pullbackPushforwardAdjunction U.ι).homEquiv
        (Scheme.Hom.relativeDifferentials f)
        (Scheme.Hom.relativeDifferentials (f.resLE V U e))
        (Scheme.Hom.relativeDifferentialsMap U.ι f (f.resLE V U e) V.ι
          (resLE_square f V U e)) :=
  ((Scheme.Modules.restrictAdjunction U.ι).homEquiv_naturality_right _ _).trans
    (Eq.trans
      (congrArg (fun t => t ≫ (Scheme.Modules.pushforward U.ι).map
          (Scheme.Hom.relativeDifferentialsMap U.ι f (f.resLE V U e) V.ι
            (resLE_square f V U e)))
        (Adjunction.homEquiv_leftAdjointUniq_hom_app
          (Scheme.Modules.restrictAdjunction U.ι)
          (Scheme.Modules.pullbackPushforwardAdjunction U.ι)
          (Scheme.Hom.relativeDifferentials f)))
      ((Scheme.Modules.pullbackPushforwardAdjunction U.ι).homEquiv_unit _ _ _).symm)

/-- The universal differential of a section coming from `U` is the restriction of the universal
differential of the corresponding section on `X`. -/
private theorem universalDerivation_d_appIso_inv_app (W : X.Opens) (a : Γ(X, W)) :
    (Scheme.Hom.universalRelativeDerivation f).d
        (((U.ι.appIso (U.ι ⁻¹ᵁ W)).inv).hom ((U.ι.app W).hom a)) =
      ((Scheme.Hom.relativeDifferentials f).val.map
        (homOfLE (U.ι.image_preimage_le W)).op).hom
        ((Scheme.Hom.universalRelativeDerivation f).d a) :=
  (congrArg (fun z => (Scheme.Hom.universalRelativeDerivation f).d z)
    (congrArg (fun gg => (CommRingCat.Hom.hom gg) a) (Scheme.Hom.app_appIso_inv U.ι W))).trans
    ((Scheme.Hom.universalRelativeDerivation f).d_map
      (homOfLE (U.ι.image_preimage_le W)).op a)

/-- `toRestrict` carries universal relative differentials of `f` to universal relative
differentials of the restricted morphism, stated on an open of `U` presented as the preimage
of its image. -/
theorem toRestrict_d_aux (W : U.toScheme.Opens)
    (y : Γ(U.toScheme, U.ι ⁻¹ᵁ (U.ι ''ᵁ W))) :
    ((toRestrict f V U e).val.app (op (U.ι ⁻¹ᵁ (U.ι ''ᵁ W)))).hom
        ((Scheme.Hom.universalRelativeDerivation f).d
          (((U.ι.appIso (U.ι ⁻¹ᵁ (U.ι ''ᵁ W))).inv).hom y)) =
      (Scheme.Hom.universalRelativeDerivation (f.resLE V U e)).d y := by
  have hc : Scheme.Hom.IsRelativeDifferentialsMap U.ι f (f.resLE V U e)
      (Scheme.Hom.relativeDifferentialsMap U.ι f (f.resLE V U e) V.ι
        (resLE_square f V U e)) :=
    (Scheme.Hom.isRelativeDifferentialsMap_iff_eq U.ι f (f.resLE V U e) V.ι
      (resLE_square f V U e) _).mpr rfl
  have hya : (U.ι.app (U.ι ''ᵁ W)).hom ((inv (U.ι.app (U.ι ''ᵁ W))).hom y) = y :=
    congrArg (fun g => (CommRingCat.Hom.hom g) y) (IsIso.inv_hom_id (U.ι.app (U.ι ''ᵁ W)))
  have h1 := hc (U.ι ''ᵁ W) ((inv (U.ι.app (U.ι ''ᵁ W))).hom y)
  rw [← restrictAdjunction_homEquiv_toRestrict f V U e,
    Adjunction.homEquiv_unit] at h1
  refine Eq.trans ?_ (h1.trans (congrArg
    (fun z => (Scheme.Hom.universalRelativeDerivation (f.resLE V U e)).d z) hya))
  exact congrArg
    (fun z => ((toRestrict f V U e).val.app (op (U.ι ⁻¹ᵁ (U.ι ''ᵁ W)))).hom z)
    ((congrArg (fun z => (Scheme.Hom.universalRelativeDerivation f).d
      (((U.ι.appIso (U.ι ⁻¹ᵁ (U.ι ''ᵁ W))).inv).hom z)) hya).symm.trans
      (universalDerivation_d_appIso_inv_app f U (U.ι ''ᵁ W) _))

/-- `toRestrict` carries the universal relative differential of a section of the structure
sheaf of `X` coming from `U` to the universal relative differential of the restricted
morphism. -/
theorem toRestrict_d (W : U.toScheme.Opens) (x : Γ(U.toScheme, W)) :
    ((toRestrict f V U e).val.app (op W)).hom
        ((Scheme.Hom.universalRelativeDerivation f).d (((U.ι.appIso W).inv).hom x)) =
      (Scheme.Hom.universalRelativeDerivation (f.resLE V U e)).d x := by
  have h := toRestrict_d_aux f V U e W
  rw [Scheme.Hom.preimage_image_eq] at h
  exact h x

/-! ### The two morphisms are mutually inverse -/

/-- `toRestrict` carries the restricted derivation to the universal relative derivation of
the restricted morphism. -/
theorem restrictedDerivation_postcomp_toRestrict :
    (restrictedDerivation f V U e).postcomp (toRestrict f V U e).val =
      Scheme.Hom.universalRelativeDerivation (f.resLE V U e) := by
  ext W x
  exact toRestrict_d f V U e W.unop x

/-- The transpose of a morphism out of the restriction, evaluated on the universal relative
differential of a section of the structure sheaf of `X`. -/
theorem restrictAdjunction_homEquiv_d {F : U.toScheme.Modules}
    (g : Scheme.Modules.restrict (Scheme.Hom.relativeDifferentials f) U.ι ⟶ F)
    (W : X.Opens) (a : Γ(X, W)) :
    ((((Scheme.Modules.restrictAdjunction U.ι).homEquiv
          (Scheme.Hom.relativeDifferentials f) F) g).val.app (op W)).hom
        ((Scheme.Hom.universalRelativeDerivation f).d a) =
      ((restrictedDerivation f V U e).postcomp g.val).d ((U.ι.app W).hom a) := by
  rw [Adjunction.homEquiv_unit]
  refine congrArg (fun z => (g.val.app (op (U.ι ⁻¹ᵁ W))).hom z) ?_
  exact (universalDerivation_d_appIso_inv_app f U W a).symm

/-- A morphism out of the restriction of the relative differentials is determined by its
effect on the restricted derivation. -/
theorem hom_ext_of_postcomp {F : U.toScheme.Modules}
    (g g' : Scheme.Modules.restrict (Scheme.Hom.relativeDifferentials f) U.ι ⟶ F)
    (h : (restrictedDerivation f V U e).postcomp g.val =
      (restrictedDerivation f V U e).postcomp g'.val) : g = g' := by
  refine ((Scheme.Modules.restrictAdjunction U.ι).homEquiv
    (Scheme.Hom.relativeDifferentials f) F).injective ?_
  refine (SheafOfModules.universalDerivation_isUniversal (inverseImageStructureMap f)
    ((Scheme.Modules.pushforward U.ι).obj F)
    ((Scheme.Hom.universalRelativeDerivation f).postcomp
      (((Scheme.Modules.restrictAdjunction U.ι).homEquiv
        (Scheme.Hom.relativeDifferentials f) F) g).val)).unique rfl ?_
  ext W a
  exact ((restrictAdjunction_homEquiv_d f V U e g' W.unop a).trans
      (PresheafOfModulesOfCommRing.Derivation.congr_d h.symm _)).trans
    (restrictAdjunction_homEquiv_d f V U e g W.unop a).symm

/-- The two comparison morphisms compose to the identity of the relative differentials of
the restricted morphism. -/
theorem fromRestrict_comp_toRestrict :
    fromRestrict f V U e ≫ toRestrict f V U e = 𝟙 _ :=
  (SheafOfModules.universalDerivation_isUniversal
    (inverseImageStructureMap (f.resLE V U e)) _
    (Scheme.Hom.universalRelativeDerivation (f.resLE V U e))).unique
    ((congrArg (fun D => D.postcomp (toRestrict f V U e).val)
      (fromRestrict_spec f V U e)).trans (restrictedDerivation_postcomp_toRestrict f V U e))
    rfl

/-- The two comparison morphisms compose to the identity of the restriction of the relative
differentials. -/
theorem toRestrict_comp_fromRestrict :
    toRestrict f V U e ≫ fromRestrict f V U e = 𝟙 _ :=
  hom_ext_of_postcomp f V U e _ _
    ((congrArg (fun D => D.postcomp (fromRestrict f V U e).val)
      (restrictedDerivation_postcomp_toRestrict f V U e)).trans (fromRestrict_spec f V U e))

/-- The restriction of the relative differentials of `f` to `U` is the relative differentials
of the restricted morphism. -/
noncomputable def restrictIso :
    Scheme.Modules.restrict (Scheme.Hom.relativeDifferentials f) U.ι ≅
      Scheme.Hom.relativeDifferentials (f.resLE V U e) where
  hom := toRestrict f V U e
  inv := fromRestrict f V U e
  hom_inv_id := toRestrict_comp_fromRestrict f V U e
  inv_hom_id := fromRestrict_comp_toRestrict f V U e

/-- Restricting a morphism of schemes to compatible open subschemes identifies the
restriction of its sheaf of relative differentials with the sheaf of relative differentials
of the restricted morphism, and this is the unique identification carrying the restricted
universal derivation to the universal derivation. -/
@[stacks 01US]
theorem existsUnique_relativeDifferentials_restrict :
    ∃! i : Scheme.Modules.restrict (Scheme.Hom.relativeDifferentials f) U.ι ≅
        Scheme.Hom.relativeDifferentials (f.resLE V U e),
      ∀ (W : U.toScheme.Opens) (x : Γ(U.toScheme, W)),
        (i.hom.val.app (.op W)).hom
            ((Scheme.Modules.restrictAppIso U.ι
                (Scheme.Hom.relativeDifferentials f) W).inv.hom
              ((Scheme.Hom.universalRelativeDerivation f).d (((U.ι.appIso W).inv).hom x))) =
          (Scheme.Hom.universalRelativeDerivation (f.resLE V U e)).d x := by
  refine ⟨restrictIso f V U e, toRestrict_d f V U e, fun i hi => ?_⟩
  refine Iso.ext (hom_ext_of_postcomp f V U e _ _ ?_)
  refine Eq.trans ?_ (restrictedDerivation_postcomp_toRestrict f V U e).symm
  ext W x
  exact hi W.unop x

end Stacks.AlgebraicGeometry.DifferentialsRestrict

end
