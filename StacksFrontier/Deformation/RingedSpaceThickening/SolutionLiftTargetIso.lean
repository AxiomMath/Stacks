module

public import StacksFrontier.Cotangent.SheavesOfRings.ThickeningLiftCorrespondence
public import StacksFrontier.Deformation.Examples.Geometric.SchemeDeformationSolution
public import StacksFrontier.Deformation.RingedSpaceThickening.SolutionHomAlgebraExtension

/-!
# The thickened structure sheaf of a solution as an inverse image

Let `Q` be a solution of the deformation problem of **Stacks 08U7**: a first order thickening
`i : X ⟶ X'` of ringed spaces with a morphism `f' : X' ⟶ S'`.  The underlying map of `i` is a
homeomorphism, and the library reads `𝒪_{X'}` on the opens of `X` in two ways: as the pushforward
`Q.thickenedSheaf` along the inverse homeomorphism, and as the inverse image `i⁻¹𝒪_{X'}`, the
structure sheaf of the inverse-image ringed space `(X, i⁻¹𝒪_{X'})`.  This file identifies the two,
compatibly with the reduction to `𝒪_X` and with the algebra structures coming from any morphism
out of `X'`.

## Main definitions

* `AlgebraicGeometry.RingedSpaceThickening.DeformationSolution.thickenedSheafIsoInverseImage`:
  the isomorphism `Q.thickenedSheaf ≅ i⁻¹𝒪_{X'}`.
* `AlgebraicGeometry.RingedSpaceThickening.DeformationSolution.comorphismOnOpensSheafMap`: the
  comorphism `𝒪_T ⟶ p_* 𝒪_{X'}` of a morphism `p : X' ⟶ T`, read on the opens of `X`.

## Main results

* `DeformationSolution.thickenedSheafIsoInverseImage_hom_comp`:
  the isomorphism followed by the structure map `i⁻¹𝒪_{X'} ⟶ 𝒪_X` of `i` is the reduction.
* `DeformationSolution.ringedSpaceStructureMap_inverseImageProjection_comp_inv`:
  for any `p : X' ⟶ T`, the structure map of `(X, i⁻¹𝒪_{X'}) ⟶ X' ⟶ T`, transported to
  `Q.thickenedSheaf`, is the adjoint of the comorphism of `p` read on the opens of `X`; for
  `p = f'` it is the algebra structure `Q.thickenedSheafBase`
  (`ringedSpaceStructureMap_inverseImageProjection_comp_f'_inv`).
* `Deformation.Examples.fiberSolution_liftTargetBaseMap_comp_inv`: for the solution attached to a
  point of the fibre of the deformation category of a scheme, the target of the isomorphism is
  `AlgebraicGeometry.Scheme.liftTarget` of the special-fibre immersion, and the statement above
  reads `AlgebraicGeometry.Scheme.liftTargetBaseMap`.

## Implementation notes

The inverse of the isomorphism is the adjoint, under `i⁻¹ ⊣ i_*`, of the restriction
`𝒪_{X'} ⟶ i_* (i⁻¹)_* 𝒪_{X'}` along the round trip of opens.  It is invertible because the unit
of `i⁻¹ ⊣ i_*` at `𝒪_{X'}` is (`AlgebraicGeometry.RingedSpace.isIso_inverseImageProjection`), and
every open of `X` is the preimage of an open of `X'`.

## References

* [Stacks Project, Tag 08U7](https://stacks.math.columbia.edu/tag/08U7)
* [Stacks Project, Tag 0E3V](https://stacks.math.columbia.edu/tag/0E3V)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction AlgebraicGeometry.RingedSpace

universe u

/-- Transporting the adjoint of a map along an equality of continuous maps: if `φ` and `ψ` agree
on sections up to the restriction along the equality of preimages, their adjoints agree up to the
transport of the inverse images. -/
theorem TopCat.Sheaf.pullbackPushforwardAdjunction_homEquiv_symm_eq_eqToHom_comp
    {Z W : TopCat.{u}} {a b : Z ⟶ W} (h : a = b) {F : TopCat.Sheaf CommRingCat.{u} W}
    {E : TopCat.Sheaf CommRingCat.{u} Z}
    (φ : F ⟶ (TopCat.Sheaf.pushforward CommRingCat.{u} a).obj E)
    (ψ : F ⟶ (TopCat.Sheaf.pushforward CommRingCat.{u} b).obj E)
    (happ : ∀ V : (Opens W)ᵒᵖ, φ.hom.app V =
      ψ.hom.app V ≫ E.obj.map (eqToHom (by rw [h]) : op ((Opens.map b).obj V.unop) ⟶
        op ((Opens.map a).obj V.unop))) :
    ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} a).homEquiv F E).symm φ =
      eqToHom (by rw [h]) ≫
        ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} b).homEquiv F E).symm ψ := by
  subst h
  have hφ : φ = ψ := ObjectProperty.hom_ext _ (NatTrans.ext (funext fun V => by
    rw [happ V]; simp))
  rw [hφ, eqToHom_refl, Category.id_comp]

namespace AlgebraicGeometry.RingedSpaceThickening.DeformationSolution

variable {X S S' : RingedSpace.{u, u}} {t : S ⟶ S'} {ht : IsFirstOrderThickening t}
  {f : X ⟶ S} {G : SheafOfModules.{u} (structureSheafRing X)}
  {c : (modulePullback f).obj
    ((modulePullback t).obj (AlgebraicGeometry.SheafOfModules.idealSheaf t)) ⟶ G}
  (Q : DeformationSolution t ht f G c)

/-! ### The comparison map -/

/-- The restriction `𝒪_{X'} ⟶ i_* (i⁻¹)_* 𝒪_{X'}` along the round trip of opens
(`fromSpaceComorphism`), as a morphism of sheaves. -/
abbrev thickenedUnitSheafMap :
    Q.X'.sheaf ⟶ (TopCat.Sheaf.pushforward CommRingCat.{u} Q.i.hom.base).obj Q.thickenedSheaf :=
  ObjectProperty.homMk Q.fromSpaceComorphism

/-- The comparison `i⁻¹𝒪_{X'} ⟶ Q.thickenedSheaf`: the adjoint of `thickenedUnitSheafMap`. -/
def inverseImageToThickenedSheaf :
    (TopCat.Sheaf.pullback CommRingCat.{u} Q.i.hom.base).obj Q.X'.sheaf ⟶ Q.thickenedSheaf :=
  ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} Q.i.hom.base).homEquiv _ _).symm
    Q.thickenedUnitSheafMap

/-- The unit of `i⁻¹ ⊣ i_*` followed by the comparison is the round-trip restriction. -/
theorem unit_comp_inverseImageToThickenedSheaf :
    (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} Q.i.hom.base).unit.app
        Q.X'.sheaf ≫
      (TopCat.Sheaf.pushforward CommRingCat.{u} Q.i.hom.base).map
        Q.inverseImageToThickenedSheaf = Q.thickenedUnitSheafMap :=
  ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} Q.i.hom.base).homEquiv_unit
    Q.X'.sheaf Q.thickenedSheaf Q.inverseImageToThickenedSheaf).symm.trans
    (Equiv.apply_symm_apply _ _)

/-- The unit of `i⁻¹ ⊣ i_*` followed by the comparison is the round-trip restriction, on the
sections over an open of `X'`. -/
theorem unit_app_comp_inverseImageToThickenedSheaf_app (U : (Opens Q.X'.carrier)ᵒᵖ) :
    ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} Q.i.hom.base).unit.app
        Q.X'.sheaf).hom.app U ≫
      Q.inverseImageToThickenedSheaf.hom.app (op ((Opens.map Q.i.hom.base).obj U.unop)) =
      Q.X'.presheaf.map (eqToHom (congrArg op (Q.opens_roundTrip' U.unop).symm)) :=
  congrArg (fun m => m.hom.app U) Q.unit_comp_inverseImageToThickenedSheaf

/-- The comparison `i⁻¹𝒪_{X'} ⟶ Q.thickenedSheaf` is an isomorphism. -/
instance isIso_inverseImageToThickenedSheaf : IsIso Q.inverseImageToThickenedSheaf := by
  have hπ : IsIso (inverseImageProjection Q.X' Q.i.hom.base) :=
    isIso_inverseImageProjection Q.X' Q.i.hom.base
      ((TopCat.isIso_iff_isHomeomorph Q.i.hom.base).mp Q.i_firstOrder.1.1)
  have : IsIso (inverseImageProjection Q.X' Q.i.hom.base).hom :=
    (inducedFunctor _).map_isIso (inverseImageProjection Q.X' Q.i.hom.base)
  have hc : IsIso (inverseImageProjection Q.X' Q.i.hom.base).hom.c := inferInstance
  have key : ∀ U : (Opens Q.X'.carrier)ᵒᵖ,
      IsIso (Q.inverseImageToThickenedSheaf.hom.app (op ((Opens.map Q.i.hom.base).obj U.unop))) :=
    fun U => by
      have : IsIso (((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u}
          Q.i.hom.base).unit.app Q.X'.sheaf).hom.app U) :=
        NatIso.isIso_app_of_isIso (inverseImageProjection Q.X' Q.i.hom.base).hom.c U
      have : IsIso (((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u}
          Q.i.hom.base).unit.app Q.X'.sheaf).hom.app U ≫
          Q.inverseImageToThickenedSheaf.hom.app (op ((Opens.map Q.i.hom.base).obj U.unop))) := by
        rw [unit_app_comp_inverseImageToThickenedSheaf_app]
        exact (Q.X'.presheaf.mapIso
          (eqToIso (congrArg op (Q.opens_roundTrip' U.unop)).symm)).isIso_hom
      exact IsIso.of_isIso_comp_left (((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u}
          Q.i.hom.base).unit.app Q.X'.sheaf).hom.app U) _
  have hall : ∀ V : (Opens X.carrier)ᵒᵖ, IsIso (Q.inverseImageToThickenedSheaf.hom.app V) := by
    intro V
    have e : op ((Opens.map Q.i.hom.base).obj ((Opens.map Q.baseIso.inv).obj V.unop)) = V :=
      congrArg op (Q.opens_roundTrip V.unop)
    have h := key (op ((Opens.map Q.baseIso.inv).obj V.unop))
    revert h
    generalize op ((Opens.map Q.i.hom.base).obj ((Opens.map Q.baseIso.inv).obj V.unop)) = W at e ⊢
    subst e
    exact id
  have : IsIso Q.inverseImageToThickenedSheaf.hom := NatIso.isIso_of_isIso_app _
  exact ⟨⟨ObjectProperty.homMk (inv Q.inverseImageToThickenedSheaf.hom),
    ObjectProperty.hom_ext _ (IsIso.hom_inv_id _), ObjectProperty.hom_ext _ (IsIso.inv_hom_id _)⟩⟩

/-! ### The isomorphism with the inverse image -/

/-- **`𝒪_{X'}` read on the opens of `X` is the inverse image `i⁻¹𝒪_{X'}`**: the pushforward
`Q.thickenedSheaf` along the inverse homeomorphism is isomorphic to the inverse image along the
thickening. -/
def thickenedSheafIsoInverseImage :
    Q.thickenedSheaf ≅ (TopCat.Sheaf.pullback CommRingCat.{u} Q.i.hom.base).obj Q.X'.sheaf :=
  (asIso Q.inverseImageToThickenedSheaf).symm

/-- The inverse of `thickenedSheafIsoInverseImage` is the comparison map. -/
theorem thickenedSheafIsoInverseImage_inv :
    Q.thickenedSheafIsoInverseImage.inv = Q.inverseImageToThickenedSheaf :=
  rfl

/-- The round-trip restriction followed by the reduction is the comorphism of the thickening. -/
theorem fromSpaceComorphism_comp_reduction :
    Q.fromSpaceComorphism ≫
        (TopCat.Presheaf.pushforward CommRingCat.{u} Q.i.hom.base).map Q.thickenedReduction =
      Q.i.hom.c := by
  refine NatTrans.ext (funext fun U => ?_)
  have hnat := Q.i.hom.c.naturality (eqToHom (congrArg op (Q.opens_roundTrip' U.unop).symm))
  have hL : (Q.fromSpaceComorphism ≫
        (TopCat.Presheaf.pushforward CommRingCat.{u} Q.i.hom.base).map Q.thickenedReduction).app U =
      Q.X'.presheaf.map (eqToHom (congrArg op (Q.opens_roundTrip' U.unop).symm)) ≫
        Q.i.hom.c.app (op ((Opens.map Q.baseIso.inv).obj ((Opens.map Q.baseIso.hom).obj U.unop))) ≫
        X.presheaf.map (Q.roundTripHom (op ((Opens.map Q.i.hom.base).obj U.unop))) :=
    congrArg (fun m => Q.X'.presheaf.map
        (eqToHom (congrArg op (Q.opens_roundTrip' U.unop)).symm) ≫
        Q.i.hom.c.app (op ((Opens.map Q.baseIso.inv).obj ((Opens.map Q.baseIso.hom).obj
          U.unop))) ≫ m) (Q.pushforwardRoundTrip_hom_app (op ((Opens.map Q.i.hom.base).obj U.unop)))
  refine hL.trans (((reassoc_of% hnat) (X.presheaf.map (Q.roundTripHom _))).trans ?_)
  exact (congrArg (Q.i.hom.c.app U ≫ ·) (functor_map_comp_map_eq_id X.presheaf
    ((Opens.map Q.i.hom.base).op.map
      (eqToHom (congrArg op (Q.opens_roundTrip' U.unop)).symm)) (Q.roundTripHom _))).trans
    (Category.comp_id _)

/-- **The isomorphism `Q.thickenedSheaf ≅ i⁻¹𝒪_{X'}` is compatible with the reductions**: followed
by the structure map `i⁻¹𝒪_{X'} ⟶ 𝒪_X` of the thickening it is the reduction
`Q.thickenedSheaf ⟶ 𝒪_X`. -/
theorem thickenedSheafIsoInverseImage_hom_comp :
    Q.thickenedSheafIsoInverseImage.hom ≫ Stacks.SheafOfModules.ringedSpaceStructureMap Q.i =
      Q.thickenedSheafReduction := by
  refine (Iso.eq_inv_comp _).mp ?_
  exact (congrArg ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u}
      Q.i.hom.base).homEquiv _ _).symm
      (ObjectProperty.hom_ext _ Q.fromSpaceComorphism_comp_reduction.symm)).trans
    ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u}
      Q.i.hom.base).homEquiv_naturality_right_symm _ _)

/-! ### The algebra structure given by a morphism out of `X'` -/

variable {T : RingedSpace.{u, u}} (p : Q.X' ⟶ T)

/-- The open of `X'` lying over an open `V` of `T` is the open matching the preimage of `V` in
`X`. -/
theorem opens_map_comp_eq (V : Opens T.carrier) :
    (Opens.map p.hom.base).obj V =
      (Opens.map Q.baseIso.inv).obj ((Opens.map (Q.i.hom.base ≫ p.hom.base)).obj V) := by
  rw [Opens.map_comp_obj]
  exact (Q.opens_roundTrip' _).symm

/-- The comorphism `𝒪_T ⟶ (p ∘ i)_* 𝒪_{X'}` of a morphism `p : X' ⟶ T`, read on the opens of
`X`. -/
def comorphismOnOpensPresheafMap :
    T.presheaf ⟶ (TopCat.Presheaf.pushforward CommRingCat.{u} (Q.i.hom.base ≫ p.hom.base)).obj
      Q.thickenedPresheaf where
  app V := p.hom.c.app V ≫ Q.X'.presheaf.map (eqToHom (congrArg op (Q.opens_map_comp_eq p V.unop)))
  naturality {V W} k := by
    have hnat := p.hom.c.naturality k
    simp only [TopCat.Presheaf.pushforward_obj_map] at hnat ⊢
    rw [reassoc_of% hnat]
    simp only [Functor.comp_map, Category.assoc, ← Functor.map_comp]
    exact congrArg (fun m => p.hom.c.app V ≫ Q.X'.presheaf.map m) (Subsingleton.elim _ _)

/-- The comorphism of `p : X' ⟶ T`, read on the opens of `X`, as a morphism of sheaves. -/
abbrev comorphismOnOpensSheafMap :
    T.sheaf ⟶ (TopCat.Sheaf.pushforward CommRingCat.{u} (Q.i.hom.base ≫ p.hom.base)).obj
      Q.thickenedSheaf :=
  ObjectProperty.homMk (Q.comorphismOnOpensPresheafMap p)

/-- **The algebra structure of `i⁻¹𝒪_{X'}` given by a morphism `p : X' ⟶ T`, read on
`Q.thickenedSheaf`.**  The structure map of `(X, i⁻¹𝒪_{X'}) ⟶ X' ⟶ T` followed by the inverse of
`thickenedSheafIsoInverseImage` is the adjoint of the comorphism of `p` read on the opens of
`X`. -/
theorem ringedSpaceStructureMap_inverseImageProjection_comp_inv :
    Stacks.SheafOfModules.ringedSpaceStructureMap (inverseImageProjection Q.X' Q.i.hom.base ≫ p) ≫
        Q.thickenedSheafIsoInverseImage.inv =
      ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u}
        (Q.i.hom.base ≫ p.hom.base)).homEquiv _ _).symm (Q.comorphismOnOpensSheafMap p) := by
  refine ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u}
    (Q.i.hom.base ≫ p.hom.base)).homEquiv _ _).injective ?_
  refine ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u}
    (Q.i.hom.base ≫ p.hom.base)).homEquiv_naturality_right _ _).trans ?_
  refine (congrArg (· ≫ (TopCat.Sheaf.pushforward CommRingCat.{u}
    (Q.i.hom.base ≫ p.hom.base)).map Q.thickenedSheafIsoInverseImage.inv)
    (Equiv.apply_symm_apply _ _)).trans ((ObjectProperty.hom_ext _ (NatTrans.ext (funext fun V =>
      ?_))).trans (Equiv.apply_symm_apply _ _).symm)
  exact (Category.assoc _ _ _).trans (congrArg (p.hom.c.app V ≫ ·)
    (Q.unit_app_comp_inverseImageToThickenedSheaf_app (op ((Opens.map p.hom.base).obj V.unop))))

/-- The map underlying `(X, i⁻¹𝒪_{X'}) ⟶ X' ⟶ S'` is the composite `X ⟶ S ⟶ S'`. -/
theorem inverseImageProjection_comp_f'_base :
    (inverseImageProjection Q.X' Q.i.hom.base ≫ Q.f').hom.base = (f ≫ t).hom.base :=
  (congrArg (fun m : X ⟶ S' => m.hom.base) Q.comm :
    Q.i.hom.base ≫ Q.f'.hom.base = (f ≫ t).hom.base)

/-- **For `p = f'`, the transported structure map is the algebra structure of the extension
attached to the solution**: the structure map of `(X, i⁻¹𝒪_{X'}) ⟶ X' ⟶ S'` followed by the
inverse of `thickenedSheafIsoInverseImage` is `Q.thickenedSheafBase`, up to the transport of
inverse images along `i ∘ f' = t ∘ f`. -/
theorem ringedSpaceStructureMap_inverseImageProjection_comp_f'_inv :
    Stacks.SheafOfModules.ringedSpaceStructureMap
        (inverseImageProjection Q.X' Q.i.hom.base ≫ Q.f') ≫
        Q.thickenedSheafIsoInverseImage.inv =
      eqToHom (congrArg (fun b => (TopCat.Sheaf.pullback CommRingCat.{u} b).obj S'.sheaf)
        Q.inverseImageProjection_comp_f'_base) ≫ Q.thickenedSheafBase := by
  refine (Q.ringedSpaceStructureMap_inverseImageProjection_comp_inv Q.f').trans ?_
  refine TopCat.Sheaf.pullbackPushforwardAdjunction_homEquiv_symm_eq_eqToHom_comp
    Q.inverseImageProjection_comp_f'_base _ _ fun V => ?_
  refine (congrArg (Q.f'.hom.c.app V ≫ ·) ?_).trans (Category.assoc _ _ _).symm
  exact (congrArg Q.X'.presheaf.map (Subsingleton.elim _ _)).trans (Q.X'.presheaf.map_comp _ _)

end AlgebraicGeometry.RingedSpaceThickening.DeformationSolution

/-! ### The scheme case -/

namespace Deformation.Examples

open AlgebraicGeometry.RingedSpaceThickening

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
  {X : Over (Spec (CommRingCat.of k))} {A : ArtinianLocalAlgCat.{u, u, u} Λ k}
  (hA : IsLocalRing.maximalIdeal (A : Type u) ^ 2 = ⊥)
  (x : (schemeDeformationCategoryProjection (Λ := Λ) (k := k) X).Fiber A)

/-- For the solution attached to a point of the fibre of the deformation category of a scheme,
the target of `thickenedSheafIsoInverseImage` is `Scheme.liftTarget` of the special-fibre
immersion. -/
theorem fiberSolution_inverseImage_eq_liftTarget :
    (TopCat.Sheaf.pullback CommRingCat.{u} (fiberSolution hA x).i.hom.base).obj
        (fiberSolution hA x).X'.sheaf = Scheme.liftTarget x.1.specialMap :=
  rfl

/-- **The scheme case**: for the solution attached to a point of the fibre and a morphism
`q` out of `Spec A`, the `𝒪_T`-algebra structure `Scheme.liftTargetBaseMap` of
`Scheme.liftTarget` of the special-fibre immersion, along the structure morphism followed by `q`,
transported to the thickened structure sheaf, is the adjoint of the comorphism of that morphism
read on the opens of `X`. -/
theorem fiberSolution_liftTargetBaseMap_comp_inv {T : Scheme.{u}} (q : baseSpec A ⟶ T) :
    Scheme.liftTargetBaseMap x.1.specialMap (x.1.toBase ≫ eqToHom (congrArg baseSpec x.2) ≫ q) ≫
        (fiberSolution hA x).thickenedSheafIsoInverseImage.inv =
      ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u}
        ((fiberSolution hA x).i.hom.base ≫
          (x.1.toBase ≫ eqToHom (congrArg baseSpec x.2) ≫ q).toLRSHom.toShHom.hom.base)).homEquiv
          _ _).symm
        ((fiberSolution hA x).comorphismOnOpensSheafMap
          (x.1.toBase ≫ eqToHom (congrArg baseSpec x.2) ≫ q).toLRSHom.toShHom) :=
  (fiberSolution hA x).ringedSpaceStructureMap_inverseImageProjection_comp_inv
    (x.1.toBase ≫ eqToHom (congrArg baseSpec x.2) ≫ q).toLRSHom.toShHom

end Deformation.Examples
