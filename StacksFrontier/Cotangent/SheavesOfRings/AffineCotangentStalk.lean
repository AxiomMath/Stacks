module

public import StacksFrontier.Cotangent.SheavesOfRings.AffineCotangentComparison
public import StacksFrontier.Cotangent.SheavesOfRings.StalkCotangentGerm
public import StacksFrontier.Cotangent.LocalizationSquareQuasiIso
public import StacksFrontier.Cotangent.Spaces.RepresentableStalks
public import StacksFrontier.Topology.Sheaves.Cohomology.KFlat.TildeStalkKFlat
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.TildeStalkGerm
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.AffineChartStalkRings
public import StacksFrontier.AlgebraicGeometry.FreeStalkBasis.BiprodPowStalk

/-!
# The canonical map of Tag 08T3 at a point

Let `f : X ⟶ Y` be a morphism of schemes, `U = Spec B ⊂ X` an affine open, `V = Spec A ⊂ Y` an
affine open with `f(U) ⊂ V`, and `y` a point of `Spec B`, with image `x` in `U`. Then:

* the stalk `𝒪_{X,x}` is the localization of `B` at `y`
  (`AlgebraicGeometry.IsAffineOpen.isLocalization_stalk'`, Schemes, Lemma 01HV);
* the stalk `(f⁻¹𝒪_Y)_x` is a localization of `A`: it is the stalk `𝒪_{Y,f x}`
  (Sheaves, Lemma 008H, `AlgebraicGeometry.Scheme.Hom.zariskiInverseImageStalkIso`), which is a
  localization of `A` because `V` is affine;
* the stalk `𝒪_{Spec B, y}` is the localization of `B` at `y`, so it is identified with `𝒪_{X,x}`
  as a `B`-algebra;
* the stalk at `y` of `L_{X/Y}|_U` is the cotangent complex of `(f⁻¹𝒪_Y)_x → 𝒪_{Spec B, y}`, and
  under this identification the germ of the canonical map `L_{B/A} ⟶ Γ(L_{X/Y}|_U)` is the
  functoriality map of the square `(A → (f⁻¹𝒪_Y)_x, B → 𝒪_{Spec B, y})`.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.specStalkSquare`: the square of ring maps
  `(A → (f⁻¹𝒪_Y)_x, B → 𝒪_{Spec B, y})`.
* `AlgebraicGeometry.Scheme.Hom.restrictedStalkIso`: the stalk at `y` of `L_{X/Y}|_U` is the
  cotangent complex of `(f⁻¹𝒪_Y)_x → 𝒪_{Spec B, y}`.

## Main results

* `AlgebraicGeometry.Scheme.Hom.isLocalization_stalkSquare_map`: `𝒪_{X,x}` is the localization
  of `B` at `y`.
* `AlgebraicGeometry.Scheme.Hom.isLocalization_stalkSquare_base`: `(f⁻¹𝒪_Y)_x` is a localization
  of `A`.
* `AlgebraicGeometry.Scheme.Hom.restrictedStalkIso_hom_germ`: the germ of the canonical map on
  global sections is the functoriality map of `AlgebraicGeometry.Scheme.Hom.specStalkSquare`.
* `AlgebraicGeometry.Scheme.Hom.restrictedStalkIso_hom_smul`: the identification of the stalk is
  `B`-semilinear.

## References

* [Stacks Project, Tag 08T3](https://stacks.math.columbia.edu/tag/08T3)
* [Stacks Project, Tag 01HV](https://stacks.math.columbia.edu/tag/01HV)
* [Stacks Project, Tag 008H](https://stacks.math.columbia.edu/tag/008H)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry Opposite
open Stacks.Sheaves.ToposPushforward Stacks.Sheaves.ToposPullback

universe u

namespace AlgebraicGeometry

/-- **Schemes, Lemma 01HV, on the spectrum, over the `RingCat`-valued stalk.** The germ map
`R ⟶ 𝒪_{Spec R, y}` into the `RingCat`-valued stalk is the localization of `R` at `y`. -/
theorem isLocalization_specStalkRingHom (R : CommRingCat.{u}) (y : PrimeSpectrum R) :
    letI := Stacks.RingedSpace.structureStalkCommRing (Spec R).toRingedSpace y
    @IsLocalization.AtPrime R _ (ToType (TopCat.Presheaf.stalk (C := RingCat.{u})
      (structureSheafRing (Spec R).toRingedSpace).obj y)) _
      (Stacks.TildeStalk.specStalkRingHom R y).toAlgebra y.asIdeal _ := by
  let := Stacks.RingedSpace.structureStalkCommRing (Spec R).toRingedSpace y
  let := (specGermRingHom R y).toAlgebra
  have h := isLocalization_atPrime_specGermRingHom R y
  have h' := (IsLocalization.isLocalization_iff_of_ringEquiv y.asIdeal.primeCompl
    (ringCatStalkRingEquiv (X := Spec R) y).symm).1 h
  have heq : ((ringCatStalkRingEquiv (X := Spec R) y).symm.toRingHom.comp
      (algebraMap R (ToType ((Spec R).presheaf.stalk y)))) =
        Stacks.TildeStalk.specStalkRingHom R y := by
    ext b
    have hc := RingHom.congr_fun (ringCatStalkRingEquiv_comp_specStalkRingHom R y) b
    exact (congrArg (ringCatStalkRingEquiv (X := Spec R) y).symm hc.symm).trans
      ((ringCatStalkRingEquiv (X := Spec R) y).symm_apply_apply _)
  rwa [heq] at h'

end AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Hom

attribute [local instance] Scheme.Modules.toPresheaf_additive
  Scheme.Modules.toPresheaf_stalkFunctor_additive

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The structural homomorphism `f⁻¹𝒪_Y ⟶ 𝒪_X` of sheaves of rings on the small Zariski site of
`X`, whose cotangent complex is `L_{X/Y}`. -/
abbrev cotangentBase :
    zariskiInverseImageStructureSheaf f ⟶ X.zariskiRingedTopos.O :=
  RingedToposHom.fSharpInverseImage f.zariskiRingedToposHom

/-- The adjunct of the identity of `f⁻¹𝒪_Y` under `zariskiInverseImageAdjunction f` is the unit
`AlgebraicGeometry.Scheme.Hom.inverseImageUnit`. -/
theorem zariskiInverseImageAdjunction_homEquiv_id :
    (zariskiInverseImageAdjunction f).homEquiv Y.zariskiRingedTopos.O _ (𝟙 _) =
      inverseImageUnit f := by
  refine (Adjunction.homEquiv_unit _ _ _ _).trans ?_
  refine (congrArg (fun t => (zariskiInverseImageAdjunction f).unit.app _ ≫ t)
    (CategoryTheory.Functor.map_id ((Opens.map f.base).sheafPushforwardContinuous CommRingCat
      (Opens.grothendieckTopology ↥Y) (Opens.grothendieckTopology ↥X)) _)).trans ?_
  exact Category.comp_id _

variable {U : X.Opens} {V : Y.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V)
  (e : U ≤ f ⁻¹ᵁ V)

/-- On an open `W` of `Spec 𝒪_X(U)`, the ring map by which `𝒪_{Spec 𝒪_X(U)}(W)` acts on the
sections of a restriction along `IsAffineOpen.fromSpec` carries the restriction of a global
section `b` to the restriction of `b` to `fromSpec ''ᵁ W`. -/
theorem fromSpec_appIso_inv_res (W : (Spec Γ(X, U)).Opens) (b : Γ(X, U)) :
    (hU.fromSpec.appIso W).inv ((Spec Γ(X, U)).presheaf.map (homOfLE le_top : W ⟶ ⊤).op
        ((Scheme.ΓSpecIso Γ(X, U)).inv b)) =
      X.presheaf.map (homOfLE ((Scheme.Hom.image_mono _ le_top).trans
        hU.fromSpec_image_top.le) : hU.fromSpec ''ᵁ W ⟶ U).op b := by
  have n := ConcreteCategory.congr_hom
    (hU.fromSpec.appIso_inv_naturality (homOfLE le_top : W ⟶ ⊤).op)
    ((Scheme.ΓSpecIso Γ(X, U)).inv b)
  have t := ConcreteCategory.congr_hom (map_eqToHom_fromSpec_image_top hU) b
  have hid : (Opens.leTop (⊤ : (Spec Γ(X, U)).Opens)) = 𝟙 _ := Subsingleton.elim _ _
  rw [hid, op_id, CategoryTheory.Functor.map_id] at t
  refine n.trans ?_
  show X.presheaf.map _ ((hU.fromSpec.appIso ⊤).inv ((Scheme.ΓSpecIso Γ(X, U)).inv b)) = _
  have t' : (hU.fromSpec.appIso ⊤).inv ((Scheme.ΓSpecIso Γ(X, U)).inv b) =
      X.presheaf.map (eqToHom hU.fromSpec_image_top).op b := t.symm
  rw [t', ← ConcreteCategory.comp_apply, ← X.presheaf.map_comp]
  exact congrArg (fun i => X.presheaf.map i b) (Quiver.Hom.unop_inj (Subsingleton.elim _ _))

section Point

variable (y : PrimeSpectrum Γ(X, U))

/-- A prime of `𝒪_X(U)`, read as a point of the scheme `Spec 𝒪_X(U)`. -/
abbrev specPoint : Spec Γ(X, U) := y

/-- The image of a point of `Spec 𝒪_X(U)` lies in `U`. -/
theorem fromSpec_mem : hU.fromSpec y ∈ U :=
  show hU.fromSpec y ∈ (U : Set X) from hU.range_fromSpec ▸ Set.mem_range_self y

include e in
/-- The image in `Y` of the image of a point of `Spec 𝒪_X(U)` lies in `V`. -/
theorem fromSpec_mem_preimage : f (hU.fromSpec y) ∈ V := e (fromSpec_mem hU y)

/-- The neighbourhood `U` of `x`, as an index of the stalk. -/
abbrev nbhdU : (OpenNhds (hU.fromSpec y))ᵒᵈ := OrderDual.toDual ⟨U, fromSpec_mem hU y⟩

/-- The commutative square of ring maps `(𝒪_Y(V) → (f⁻¹𝒪_Y)_x, 𝒪_X(U) → 𝒪_{X,x})`: the square
of the canonical ring map `𝒪_Y(V) ⟶ (f⁻¹𝒪_Y)(U)` followed by the germ square at `x`. -/
abbrev stalkSquare :=
  (affineAlgebraSquare f e).comp
    (Sheaf.germSquare (cotangentBase f) (hU.fromSpec y) (nbhdU hU y))

/-- On sections over `V`, the canonical ring map to the stalk `(f⁻¹𝒪_Y)_x` is the germ at `f x`
followed by the identification `𝒪_{Y,f x} ≅ (f⁻¹𝒪_Y)_x`. -/
theorem stalkSquare_base :
    (stalkSquare f hU e y).base =
      (zariskiInverseImageStalkIso f Y.sheaf (hU.fromSpec y)).inv.hom.comp
        (TopCat.Presheaf.germ (X := Y.toTopCat) Y.sheaf.obj V (f (hU.fromSpec y))
          (fromSpec_mem_preimage f hU e y)).hom := by
  have h := germ_zariskiInverseImageStalkIso_inv f Y.sheaf (hU.fromSpec y) V
    (fromSpec_mem_preimage f hU e y)
  have hu := congrArg (fun k : Y.zariskiRingedTopos.O ⟶ _ => k.hom.app (op V))
    (zariskiInverseImageAdjunction_homEquiv_id f)
  ext a
  have h' := ConcreteCategory.congr_hom h a
  exact (TopCat.Presheaf.germ_res_apply ((zariskiInverseImageStructureSheaf f).obj) (homOfLE e)
    (hU.fromSpec y) (fromSpec_mem hU y) (((inverseImageUnit f).hom.app (op V)) a)).trans
    ((congrArg (fun t => (TopCat.Presheaf.germ ((zariskiInverseImageStructureSheaf f).obj)
        (f ⁻¹ᵁ V) (hU.fromSpec y) (fromSpec_mem_preimage f hU e y)) t)
      (ConcreteCategory.congr_hom hu a).symm).trans h'.symm)

/-- **Schemes, Lemma 01HV.** The stalk `𝒪_{X,x}` at the image `x ∈ U` of `y ∈ Spec 𝒪_X(U)` is
the localization of `𝒪_X(U)` at `y`, along the germ map of the square. -/
theorem isLocalization_stalkSquare_map :
    @IsLocalization.AtPrime Γ(X, U) _ (Sheaf.stalkRing (hU.fromSpec y) X.zariskiRingedTopos.O) _
      (stalkSquare f hU e y).map.toAlgebra y.asIdeal _ :=
  hU.isLocalization_stalk' y (fromSpec_mem hU y)

/-- **Sheaves, Lemma 008H, with Schemes, Lemma 01HV.** The stalk `(f⁻¹𝒪_Y)_x` is a localization
of `𝒪_Y(V)`, along the canonical ring map of the square: it is the stalk `𝒪_{Y,f x}`, which is a
localization of `𝒪_Y(V)` because `V` is affine. -/
theorem isLocalization_stalkSquare_base :
    @IsLocalization Γ(Y, V) _
      (hV.primeIdealOf ⟨f (hU.fromSpec y), fromSpec_mem_preimage f hU e y⟩).asIdeal.primeCompl
      (Sheaf.stalkRing (hU.fromSpec y) (zariskiInverseImageStructureSheaf f)) _
      (stalkSquare f hU e y).base.toAlgebra := by
  rw [stalkSquare_base]
  let alg := TopCat.Presheaf.algebra_section_stalk Y.presheaf
    (⟨f (hU.fromSpec y), fromSpec_mem_preimage f hU e y⟩ : V)
  have h := hV.isLocalization_stalk ⟨f (hU.fromSpec y), fromSpec_mem_preimage f hU e y⟩
  let iso := zariskiInverseImageStalkIso f Y.sheaf (hU.fromSpec y)
  let eq : Y.presheaf.stalk (f (hU.fromSpec y)) ≃+*
      Sheaf.stalkRing (hU.fromSpec y) (zariskiInverseImageStructureSheaf f) :=
    iso.symm.commRingCatIsoToRingEquiv
  have key := (@IsLocalization.isLocalization_iff_of_ringEquiv Γ(Y, V) _
    (hV.primeIdealOf ⟨f (hU.fromSpec y), fromSpec_mem_preimage f hU e y⟩).asIdeal.primeCompl
    (Y.presheaf.stalk (f (hU.fromSpec y))) _ alg
    (Sheaf.stalkRing (hU.fromSpec y) (zariskiInverseImageStructureSheaf f)) _ eq).1 h
  have hring : eq.toRingHom.comp (@algebraMap Γ(Y, V) (Y.presheaf.stalk (f (hU.fromSpec y))) _ _
      alg) = iso.inv.hom.comp
        (TopCat.Presheaf.germ (X := Y.toTopCat) Y.sheaf.obj V (f (hU.fromSpec y))
          (fromSpec_mem_preimage f hU e y)).hom :=
    RingHom.ext fun _ => rfl
  rwa [← hring]

/-- The stalk `𝒪_{X,x}` is identified with the `RingCat`-valued stalk `𝒪_{Spec B, y}`, as the
unique isomorphism of `B`-algebras between two localizations of `B` at `y`. -/
def stalkRingEquiv :
    letI := Stacks.RingedSpace.structureStalkCommRing (Spec Γ(X, U)).toRingedSpace y
    Sheaf.stalkRing (hU.fromSpec y) X.zariskiRingedTopos.O ≃+*
      ToType (TopCat.Presheaf.stalk (C := RingCat.{u})
        (structureSheafRing (Spec Γ(X, U)).toRingedSpace).obj y) :=
  let := Stacks.RingedSpace.structureStalkCommRing (Spec Γ(X, U)).toRingedSpace y
  let : Algebra Γ(X, U) (Sheaf.stalkRing (hU.fromSpec y) X.zariskiRingedTopos.O) :=
    (stalkSquare f hU e y).map.toAlgebra
  let : Algebra Γ(X, U) (ToType (TopCat.Presheaf.stalk (C := RingCat.{u})
      (structureSheafRing (Spec Γ(X, U)).toRingedSpace).obj y)) :=
    (Stacks.TildeStalk.specStalkRingHom Γ(X, U) y).toAlgebra
  have := isLocalization_stalkSquare_map f hU e y
  have := isLocalization_specStalkRingHom Γ(X, U) y
  (IsLocalization.algEquiv y.asIdeal.primeCompl
    (Sheaf.stalkRing (hU.fromSpec y) X.zariskiRingedTopos.O)
    (ToType (TopCat.Presheaf.stalk (C := RingCat.{u})
      (structureSheafRing (Spec Γ(X, U)).toRingedSpace).obj y))).toRingEquiv

include e in
/-- The identification `𝒪_{X,x} ≅ 𝒪_{Spec B, y}` is compatible with the two maps from `B`. -/
theorem stalkRingEquiv_map (b : Γ(X, U)) :
    stalkRingEquiv f hU e y ((stalkSquare f hU e y).map b) =
      Stacks.TildeStalk.specStalkRingHom Γ(X, U) y b := by
  let := Stacks.RingedSpace.structureStalkCommRing (Spec Γ(X, U)).toRingedSpace y
  let : Algebra Γ(X, U) (Sheaf.stalkRing (hU.fromSpec y) X.zariskiRingedTopos.O) :=
    (stalkSquare f hU e y).map.toAlgebra
  let : Algebra Γ(X, U) (ToType (TopCat.Presheaf.stalk (C := RingCat.{u})
      (structureSheafRing (Spec Γ(X, U)).toRingedSpace).obj y)) :=
    (Stacks.TildeStalk.specStalkRingHom Γ(X, U) y).toAlgebra
  dsimp only [stalkRingEquiv]
  exact AlgEquiv.commutes _ b

/-- The `RingCat`-valued stalk `𝒪_{Spec B, y}`, as an algebra over `(f⁻¹𝒪_Y)_x` through
`𝒪_{X,x}`. -/
abbrev specStalkAlgebra :
    CommAlgCat.{u} (Sheaf.stalkRing (hU.fromSpec y) (zariskiInverseImageStructureSheaf f)) :=
  let := Stacks.RingedSpace.structureStalkCommRing (Spec Γ(X, U)).toRingedSpace y
  let : Algebra (Sheaf.stalkRing (hU.fromSpec y) (zariskiInverseImageStructureSheaf f))
      (ToType (TopCat.Presheaf.stalk (C := RingCat.{u})
        (structureSheafRing (Spec Γ(X, U)).toRingedSpace).obj y)) :=
    ((stalkRingEquiv f hU e y).toRingHom.comp
      (Sheaf.stalkMap (cotangentBase f) (hU.fromSpec y)).hom).toAlgebra
  CommAlgCat.of _ (ToType (TopCat.Presheaf.stalk (C := RingCat.{u})
    (structureSheafRing (Spec Γ(X, U)).toRingedSpace).obj y))

/-- The square transporting `𝒪_{X,x}` to `𝒪_{Spec B, y}` over `(f⁻¹𝒪_Y)_x`. -/
def stalkTransportSquare :
    CommAlgCat.AlgebraSquare.{u, u, u}
      (Sheaf.stalkRing (hU.fromSpec y) (zariskiInverseImageStructureSheaf f))
      (Sheaf.stalkRing (hU.fromSpec y) (zariskiInverseImageStructureSheaf f))
      (Sheaf.stalkAlgebra (cotangentBase f) (hU.fromSpec y)) (specStalkAlgebra f hU e y) where
  base := RingHom.id _
  map := (stalkRingEquiv f hU e y).toRingHom
  map_algebraMap _ := rfl

/-- The inverse square, transporting `𝒪_{Spec B, y}` back to `𝒪_{X,x}`. -/
def stalkTransportSquareInv :
    CommAlgCat.AlgebraSquare.{u, u, u}
      (Sheaf.stalkRing (hU.fromSpec y) (zariskiInverseImageStructureSheaf f))
      (Sheaf.stalkRing (hU.fromSpec y) (zariskiInverseImageStructureSheaf f))
      (specStalkAlgebra f hU e y) (Sheaf.stalkAlgebra (cotangentBase f) (hU.fromSpec y)) where
  base := RingHom.id _
  map := (stalkRingEquiv f hU e y).symm.toRingHom
  map_algebraMap _ := (stalkRingEquiv f hU e y).symm_apply_apply _

/-- The square `(𝒪_Y(V) → (f⁻¹𝒪_Y)_x, 𝒪_X(U) → 𝒪_{Spec B, y})` of the stalkwise step. -/
def specStalkSquare :
    CommAlgCat.AlgebraSquare.{u, u, u} Γ(Y, V)
      (Sheaf.stalkRing (hU.fromSpec y) (zariskiInverseImageStructureSheaf f))
      (affineAlgebra f e) (specStalkAlgebra f hU e y) where
  base := (stalkSquare f hU e y).base
  map := Stacks.TildeStalk.specStalkRingHom Γ(X, U) y
  map_algebraMap a :=
    (stalkRingEquiv_map f hU e y _).symm.trans
      (congrArg (stalkRingEquiv f hU e y) ((stalkSquare f hU e y).map_algebraMap a))

/-- The square `AlgebraicGeometry.Scheme.Hom.specStalkSquare` is the square
`AlgebraicGeometry.Scheme.Hom.stalkSquare` followed by the transport of `𝒪_{X,x}` to
`𝒪_{Spec B, y}`. -/
theorem specStalkSquare_eq :
    specStalkSquare f hU e y = (stalkSquare f hU e y).comp (stalkTransportSquare f hU e y) :=
  CommAlgCat.algebraSquare_ext rfl (RingHom.ext fun b => (stalkRingEquiv_map f hU e y b).symm)

/-- `𝒪_{X,x}` and `𝒪_{Spec B, y}` have isomorphic cotangent complexes over `(f⁻¹𝒪_Y)_x`. -/
def stalkTransportIso :=
  CommAlgCat.cotangentComplexAbIsoOfSquares (stalkTransportSquare f hU e y)
    (stalkTransportSquareInv f hU e y)
    (CommAlgCat.algebraSquare_ext rfl
      (RingHom.ext fun b => (stalkRingEquiv f hU e y).symm_apply_apply b))
    (CommAlgCat.algebraSquare_ext rfl
      (RingHom.ext fun b => (stalkRingEquiv f hU e y).apply_symm_apply b))

/-- **The stalk at `y` of `L_{X/Y}|_U`.** The stalk at `y ∈ Spec B` of the restriction of
`L_{X/Y}` to `U = Spec B` is, as a complex of abelian groups, the cotangent complex of
`(f⁻¹𝒪_Y)_x → 𝒪_{Spec B, y}`. -/
def restrictedStalkIso :
    ((Scheme.Modules.toPresheaf (Spec Γ(X, U)) ⋙
        TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (specPoint y)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj (restrictedCotangentComplex f hU) ≅
      CommAlgCat.cotangentComplexAb.{u, u}
        (Sheaf.stalkRing (hU.fromSpec y) (zariskiInverseImageStructureSheaf f))
        (specStalkAlgebra f hU e y) :=
  (NatIso.mapHomologicalComplex (Scheme.Modules.restrictStalkNatIso hU.fromSpec
      (specPoint y))
      (ComplexShape.up ℤ)).app f.cotangentComplex ≪≫
    Sheaf.cotangentComplexStalkAbIso (cotangentBase f) (hU.fromSpec y) ≪≫
    stalkTransportIso f hU e y

/-- **The germ at `y` of the canonical map on global sections.** The identification of the stalk
at `y` of `L_{X/Y}|_U` with `L_{𝒪_{Spec B, y}/(f⁻¹𝒪_Y)_x}` sends the germ of the image of
`m ∈ L_{B/A}` under the canonical map `L_{B/A} ⟶ Γ(L_{X/Y}|_U)` to the image of `m` under the
functoriality map of the square `(A → (f⁻¹𝒪_Y)_x, B → 𝒪_{Spec B, y})`. -/
theorem restrictedStalkIso_hom_germ (k : ℤ)
    (m : (CommAlgCat.cotangentComplex.{u, u} Γ(Y, V) (affineAlgebra f e)).X k) :
    (restrictedStalkIso f hU e y).hom.f k
        (TopCat.Presheaf.germ (C := AddCommGrpCat.{u})
          ((restrictedCotangentComplex f hU).X k).presheaf ⊤ (specPoint y) trivial
          ((gammaCotangentComparison f hU e).f k m)) =
      (CommAlgCat.cotangentComplexAbMap (specStalkSquare f hU e y)).f k m := by
  let L : X.Modules := f.cotangentComplex.X k
  let c : L.presheaf.obj (op U) := (cotangentSectionsComparison f e).f k m
  have ha : (Scheme.Modules.restrictStalkNatIso hU.fromSpec (specPoint y)).hom.app L
      (TopCat.Presheaf.germ (C := AddCommGrpCat.{u})
        ((restrictedCotangentComplex f hU).X k).presheaf ⊤ (specPoint y) trivial
        ((gammaCotangentComparison f hU e).f k m)) =
      TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) L.presheaf U (hU.fromSpec y)
        (fromSpec_mem hU y) c := by
    have h₁ := ConcreteCategory.congr_hom (Scheme.Modules.germ_restrictStalkNatIso_hom_app
      hU.fromSpec (specPoint y) L (U := ⊤) trivial) ((gammaCotangentComparison f hU e).f k m)
    exact h₁.trans (TopCat.Presheaf.germ_res_apply L.presheaf
      (eqToHom (hU.fromSpec_image_top)) (hU.fromSpec y) _ c)
  have hd := Sheaf.cotangentComplexStalkAbIso_hom_germ (cotangentBase f) (hU.fromSpec y) k U
    (fromSpec_mem hU y) ((CommAlgCat.squareCotangentComplexMap.{u, u, u}
      (affineAlgebraSquare f e)).f k m)
  have hsq₁ := CommAlgCat.squareCotangentComplexMap_comp_apply.{u} (affineAlgebraSquare f e)
    (Sheaf.germSquare (cotangentBase f) (hU.fromSpec y) (nbhdU hU y)) k m
  have hsq₂ := CommAlgCat.squareCotangentComplexMap_apply_of_eq_comp.{u}
    (stalkSquare f hU e y) (stalkTransportSquare f hU e y) (specStalkSquare_eq f hU e y) k m
  show (CommAlgCat.cotangentComplexAbMap (stalkTransportSquare f hU e y)).f k
      ((Sheaf.cotangentComplexStalkAbIso (cotangentBase f) (hU.fromSpec y)).hom.f k
        ((Scheme.Modules.restrictStalkNatIso hU.fromSpec (specPoint y)).hom.app L
          (TopCat.Presheaf.germ (C := AddCommGrpCat.{u})
            ((restrictedCotangentComplex f hU).X k).presheaf ⊤ (specPoint y) trivial
            ((gammaCotangentComparison f hU e).f k m)))) = _
  rw [ha]
  exact (congrArg (fun z => (CommAlgCat.cotangentComplexAbMap
    (stalkTransportSquare f hU e y)).f k z) (hd.trans hsq₁.symm)).trans hsq₂.symm

/-- **The identification of the stalk at `y` of `L_{X/Y}|_U` is `B`-semilinear.** For `b ∈ B`,
multiplying by the germ of `b` on the stalk of `L_{X/Y}|_U` corresponds to multiplying by its
image in `𝒪_{Spec B, y}` on `L_{𝒪_{Spec B, y}/(f⁻¹𝒪_Y)_x}`. -/
theorem restrictedStalkIso_hom_smul (k : ℤ) (b : Γ(X, U))
    (w : (Stacks.TildeStalk.specStalkFunctor Γ(X, U) (specPoint y)).obj
      ((restrictedCotangentComplex f hU).X k)) :
    (restrictedStalkIso f hU e y).hom.f k (Stacks.TildeStalk.specStalkRingHom Γ(X, U) y b • w) =
      (show ((CommAlgCat.cotangentComplex.{u, u} _ (specStalkAlgebra f hU e y)).X k : Type u) from
        (show (specStalkAlgebra f hU e y : Type u) from
          Stacks.TildeStalk.specStalkRingHom Γ(X, U) y b) •
        (show ((CommAlgCat.cotangentComplex.{u, u} _ (specStalkAlgebra f hU e y)).X k : Type u)
          from (restrictedStalkIso f hU e y).hom.f k w)) := by
  let R : (Spec Γ(X, U)).Modules := (restrictedCotangentComplex f hU).X k
  let L : X.Modules := f.cotangentComplex.X k
  let O := structureSheafRing (Spec Γ(X, U)).toRingedSpace
  obtain ⟨W, hyW, r, rfl⟩ := TopCat.Presheaf.exists_germ_eq (C := AddCommGrpCat.{u}) R.presheaf w
  let s₀ : (Spec Γ(X, U)).ringCatSheaf.obj.obj (op W) :=
    (Spec Γ(X, U)).presheaf.map (homOfLE le_top : W ⟶ ⊤).op ((Scheme.ΓSpecIso Γ(X, U)).inv b)
  let r' : R.val.obj (op W) := r
  have hι : Stacks.TildeStalk.specStalkRingHom Γ(X, U) y b =
      (TopCat.Presheaf.germ (C := RingCat.{u}) O.obj W (specPoint y) hyW).hom s₀ :=
    (TopCat.Presheaf.germ_res_apply O.obj (homOfLE le_top : W ⟶ ⊤) (specPoint y) hyW
      ((Scheme.ΓSpecIso Γ(X, U)).inv b)).symm
  have hsm : Stacks.TildeStalk.specStalkRingHom Γ(X, U) y b •
      (show (Stacks.TildeStalk.specStalkFunctor Γ(X, U) (specPoint y)).obj R from
        (TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) R.presheaf W (specPoint y) hyW) r) =
      (TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) R.presheaf W (specPoint y) hyW)
        (s₀ • r') := by
    rw [hι]
    exact (AlgebraicGeometry.SheafOfModules.germ_hom_smul O (specPoint y) R.val W hyW s₀ r').symm
  let W' : X.Opens := hU.fromSpec ''ᵁ W
  have hxW' : hU.fromSpec y ∈ W' := ⟨y, hyW, rfl⟩
  let c' : X.ringCatSheaf.obj.obj (op W') := (hU.fromSpec.appIso W).inv s₀
  let r'' : L.val.obj (op W') := r
  have hcr : (s₀ • r' : R.val.obj (op W)) = (c' • r'' : L.val.obj (op W')) := rfl
  have hR : ∀ z : R.presheaf.obj (op W),
      (Scheme.Modules.restrictStalkNatIso hU.fromSpec (specPoint y)).hom.app L
        ((TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) R.presheaf W (specPoint y) hyW) z) =
      TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) L.presheaf W' (hU.fromSpec y) hxW' z :=
    fun z => ConcreteCategory.congr_hom (Scheme.Modules.germ_restrictStalkNatIso_hom_app
      hU.fromSpec (specPoint y) L hyW) z
  have hX := Sheaf.cotangentComplexStalkAbIso_hom_germ_smul (cotangentBase f) (hU.fromSpec y) k W'
    hxW' c' r''
  have hgerm : (Sheaf.germSquare (cotangentBase f) (hU.fromSpec y)
      (OrderDual.toDual ⟨W', hxW'⟩)).map c' = (stalkSquare f hU e y).map b := by
    show (TopCat.Presheaf.germ X.presheaf W' (hU.fromSpec y) hxW').hom
      ((hU.fromSpec.appIso W).inv ((Spec Γ(X, U)).presheaf.map (homOfLE le_top : W ⟶ ⊤).op
        ((Scheme.ΓSpecIso Γ(X, U)).inv b))) = _
    rw [fromSpec_appIso_inv_res]
    exact TopCat.Presheaf.germ_res_apply X.presheaf _ (hU.fromSpec y) hxW' b
  let Tx := (Sheaf.cotangentComplexStalkAbIso (cotangentBase f) (hU.fromSpec y)).hom.f k
  let Tt := (CommAlgCat.cotangentComplexAbMap (stalkTransportSquare f hU e y)).f k
  let M := ((CommAlgCat.cotangentComplex.{u, u} _ (specStalkAlgebra f hU e y)).X k : Type u)
  let P : ↑(specStalkAlgebra f hU e y) → M → M := fun t z => t • z
  let N := ((CommAlgCat.cotangentComplex.{u, u}
    (Sheaf.stalkRing (hU.fromSpec y) (zariskiInverseImageStructureSheaf f))
    (Sheaf.stalkAlgebra (cotangentBase f) (hU.fromSpec y))).X k : Type u)
  let Q : ↑(Sheaf.stalkAlgebra (cotangentBase f) (hU.fromSpec y)) → N → N := fun t z => t • z
  have hTdef : ∀ z, (restrictedStalkIso f hU e y).hom.f k z =
      Tt (Tx ((Scheme.Modules.restrictStalkNatIso hU.fromSpec (specPoint y)).hom.app L z)) :=
    fun _ => rfl
  have hT : ∀ z : N,
      Tt (Q ((stalkSquare f hU e y).map b) z) =
        P (Stacks.TildeStalk.specStalkRingHom Γ(X, U) y b) (Tt z) := fun z =>
    (((CommAlgCat.squareCotangentComplexMap.{u, u, u} (stalkTransportSquare f hU e y)).f
      k).hom.map_smul ((stalkSquare f hU e y).map b) z).trans
      (congrArg (fun t => P t (Tt z)) (stalkRingEquiv_map f hU e y b))
  let g := TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) L.presheaf W' (hU.fromSpec y) hxW'
  refine (congrArg ((restrictedStalkIso f hU e y).hom.f k) hsm).trans ?_
  refine (hTdef _).trans ((congrArg (fun z => Tt (Tx z))
    ((hR _).trans (congrArg g hcr))).trans ?_)
  refine (congrArg Tt (hX.trans (by rw [hgerm]; rfl : _ = Q ((stalkSquare f hU e y).map b)
    (Tx (g r''))))).trans ?_
  exact (hT _).trans (congrArg (P _) ((congrArg (fun z => Tt (Tx z)) (hR r)).symm.trans
    (hTdef _).symm))

end Point

end AlgebraicGeometry.Scheme.Hom


end
