module

public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Category.Ring.FinitePresentation
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.RingTheory.Etale.Field
public import Mathlib.RingTheory.TensorProduct.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GeometricPointFiber
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HenselianRings.HenselizationTower
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HenselianRings.EtaleLocalRing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HenselianRings.SchemeLocalRings
public import StacksFrontier.AlgebraicGeometry.Size.FiniteType
public import StacksFrontier.AlgebraicGeometry.Size.Monomorphism
public import StacksFrontier.AlgebraicGeometry.Topologies.SmallEtaleStructureSheaf
public import StacksFrontier.RingTheory.Henselian.StrictHenselizationColimit
public import StacksFrontier.RingTheory.Henselian.EtaleLifting
import all StacksFrontier.AlgebraicGeometry.EtaleCohomology.HenselianRings.EtaleLocalRing

/-!
# The étale local ring at a geometric point

Let `s` be a geometric point of a scheme `S`, lying over the point `x` of `S`, and let `B` be a
big étale site containing `S`. The stalk at `s` of the structure sheaf of the small étale site
of `S` is the *étale local ring* of `S` at `s`. It carries two canonical maps: the ordinary
local ring `𝒪_{S,x}` maps to it, because an ordinary open neighbourhood of `x` is in particular
an étale neighbourhood of `s`, and it maps to the field of `s`, by evaluating a germ at the
chosen lift of `s`.

The étale local ring is the strict henselization of `𝒪_{S,x}` relative to the separable closure
of `κ(x)` inside the field of `s`, and the comparison is uniquely determined by its
compatibility with those two maps.

The two canonical maps `AlgebraicGeometry.structureSheafStalkFromLocalRing` and
`AlgebraicGeometry.structureSheafStalkToGeometricField`, the algebra structure
`AlgebraicGeometry.geometricResidueAlgebra` they induce on the field of the point, their
characterizations on an étale neighbourhood, the étale neighbourhoods read off an ordinary
open neighbourhood or off an augmented étale algebra, and the comparison
`AlgebraicGeometry.etaleLocalRing_strictHenselization_canonical` together with its uniqueness
`AlgebraicGeometry.etaleLocalRing_strictHenselization_unique` are in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.HenselianRings.EtaleLocalRing`, which this
module imports.

## Main definitions

* `AlgebraicGeometry.zariskiStalkCocone` and `AlgebraicGeometry.geometricEvaluationCocone` are
  the two cocones on the étale structure presheaf that the canonical maps out of the stalk are
  descended from.

## Main results

* `AlgebraicGeometry.nonempty_etaleLocalRing_strictHenselization_comparison`: a comparison
  isomorphism compatible with both canonical maps exists.  This is the existence half of the
  identification of the étale local ring with the strict henselization of the ordinary local
  ring formed using the relative separable closure inside the geometric point's field.

## Implementation notes

The separable closure used is the relative separable closure *inside* the geometric point's
field, not an abstract copy of it, so that evaluation of germs lands in the field of the point
on the nose.

The comparison is obtained by presenting both sides as filtered colimits over the étale
algebras augmented towards the field of the point: the strict henselization because it is
ind-étale over the local ring, and the stalk because the affine étale neighbourhoods coming
from such algebras are cofinal among all étale neighbourhoods. Uniqueness then follows from
the universal property of the henselization applied to each stage of that presentation.

## References

* [Stacks Project, Tag 04HX](https://stacks.math.columbia.edu/tag/04HX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite IsLocalRing

open scoped TensorProduct

universe u

namespace AlgebraicGeometry

/-- An algebra endomorphism of an ind-étale henselian local algebra which induces the identity
on the residue field is the identity: each étale stage of the presentation lifts its residual
map uniquely, so the endomorphism fixes every stage. -/
private theorem algHom_eq_id_of_residue_eq {R H : Type u} [CommRing R] [CommRing H]
    [HenselianLocalRing H] [Algebra R H]
    (hind : (CommAlgCat.etale.{u} R).ind.{u} (CommAlgCat.of R H)) (φ : H →ₐ[R] H)
    (hφ : ∀ a, residue H (φ a) = residue H a) :
    φ = AlgHom.id R H := by
  obtain ⟨J, _, _, pres, hpres⟩ := hind
  have hlegs (j : J) : φ.comp (pres.cocone.ι.app j).hom = (pres.cocone.ι.app j).hom := by
    let A := (pres.diag.obj j : Type u)
    let leg : A →ₐ[R] H := (pres.cocone.ι.app j).hom
    let ρ : A →ₐ[R] ResidueField H :=
      { toRingHom := (residue H).comp leg.toRingHom
        commutes' := fun r => by
          change residue H (leg (algebraMap R A r)) = algebraMap R (ResidueField H) r
          rw [AlgHom.commutes, IsScalarTower.algebraMap_apply R H (ResidueField H),
            IsLocalRing.ResidueField.algebraMap_eq] }
    obtain ⟨g, -, huniq⟩ := HenselianLocalRing.existsUnique_algHom_residue_of_etale ρ
    exact (huniq (φ.comp leg) fun x => hφ (leg x)).trans (huniq leg fun _ => rfl).symm
  have hid : CommAlgCat.ofHom φ = 𝟙 (CommAlgCat.of R H) :=
    pres.isColimit.hom_ext fun j => CommAlgCat.hom_ext (hlegs j)
  exact AlgHom.ext fun a => ConcreteCategory.congr_hom hid a

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (s : GeometricPoint S)

/-- The cocone on the ordinary open neighbourhoods of the image of a geometric point whose
vertex is the stalk of the étale structure sheaf, given by viewing an ordinary neighbourhood as
an étale one. -/
public def zariskiStalkCocone :
    Cocone (((TopologicalSpace.OpenNhds.inclusion
        (s.hom (closedPoint s.residueField))).op ⋙ S.presheaf) ⋙
      forget₂ CommRingCat RingCat) := by
  classical
  let x := s.hom (closedPoint s.residueField)
  let F := (CategoryOfElements.π (geometricPointFiber B S hS s)).op ⋙
    (SmallEtale.structureSheaf B S hS).obj
  let D₀ := (TopologicalSpace.OpenNhds.inclusion x).op ⋙ S.presheaf
  let Q := forget₂ CommRingCat RingCat
  let D := D₀ ⋙ Q
  let stage : TopologicalSpace.OpenNhds x → (geometricPointFiber B S hS s).Elements :=
    fun V => zariskiNeighborhood B S hS s x rfl V
  let stageMap : {V W : TopologicalSpace.OpenNhds x} → (i : V ⟶ W) → stage V ⟶ stage W :=
    fun {_ _} i => zariskiNeighborhoodMap B S hS s x rfl i
  let eStage (V : TopologicalSpace.OpenNhds x) :
      D.obj (Opposite.op V) ≅ F.obj (Opposite.op (stage V)) :=
    (Q.mapIso (Scheme.Opens.topIso (X := S) V.1)).symm
  exact {
    pt := etaleLocalRing B S hS s
    ι := {
      app := fun V => (eStage (unop V)).hom ≫ colimit.ι F (Opposite.op (stage (unop V)))
      naturality := by
        intro V W f
        let i : (unop W) ⟶ (unop V) := f.unop
        have hle := (TopologicalSpace.OpenNhds.le_def (unop W) (unop V)).mp i.le
        have hFmap : F.map (Opposite.op (stageMap i)) = Q.map ((S.homOfLE hle).appTop) := by
          dsimp [F, SmallEtale.structureSheaf, Stacks.Sites.structurePresheaf, stageMap,
            zariskiNeighborhoodMap]
          rfl
        have hnat : D.map f ≫ (eStage (unop W)).hom =
            (eStage (unop V)).hom ≫ F.map (Opposite.op (stageMap i)) := by
          change Q.map (S.presheaf.map (homOfLE hle).op) ≫
              Q.map ((Scheme.Opens.topIso (X := S) (unop W).1).inv) =
            Q.map ((Scheme.Opens.topIso (X := S) (unop V).1).inv) ≫
              F.map (Opposite.op (stageMap i))
          rw [hFmap]
          exact congrArg Q.map (opens_topIso_homOfLE S hle)
        calc
          D.map f ≫ ((eStage (unop W)).hom ≫
              colimit.ι F (Opposite.op (stage (unop W)))) =
              ((eStage (unop V)).hom ≫ F.map (Opposite.op (stageMap i))) ≫
                colimit.ι F (Opposite.op (stage (unop W))) := by
              rw [← Category.assoc, hnat]
              rfl
          _ = (eStage (unop V)).hom ≫ colimit.ι F (Opposite.op (stage (unop V))) :=
            (Category.assoc _ _ _).trans
              (congrArg ((eStage (unop V)).hom ≫ ·) (colimit.w F (Opposite.op (stageMap i))))
    }
  }

/-- The cocone on the étale neighbourhoods of a geometric point whose vertex is the field of the
point, given by evaluating a section at the chosen lift of the point. -/
public def geometricEvaluationCocone :
    Cocone ((CategoryOfElements.π (geometricPointFiber B S hS s)).op ⋙
      (SmallEtale.structureSheaf B S hS).obj) where
  pt := RingCat.of s.residueField
  ι :=
    { app := fun U => RingCat.ofHom
        (((U.unop.2.1).appTop ≫ (Scheme.ΓSpecIso (.of s.residueField)).hom).hom)
      naturality := by
        intro U V f
        dsimp [SmallEtale.structureSheaf, Stacks.Sites.structurePresheaf,
          CategoryOfElements.π]
        apply RingCat.hom_ext
        ext a
        let g : (SmallEtale.toScheme B S hS).obj V.unop.1 ⟶
            (SmallEtale.toScheme B S hS).obj U.unop.1 :=
          Over.Hom.left ((Over.post B.inclusion).map f.unop.1.hom)
        change (Scheme.ΓSpecIso (.of s.residueField)).hom.hom
            ((g.appTop ≫ (V.unop.2.1).appTop) a) =
          (Scheme.ΓSpecIso (.of s.residueField)).hom.hom ((U.unop.2.1).appTop a)
        have hp : V.unop.2.1 ≫ g = U.unop.2.1 := by
          simpa [geometricPointFiber, g] using congrArg Subtype.val f.unop.2
        rw [← Scheme.Hom.comp_appTop, hp] }

/-- An étale neighbourhood which is isomorphic over `S` to an ordinary open neighbourhood of the
image of the geometric point receives the germ of a section over that open as the class of the
transported section. -/
private theorem structureSheafStalkFromLocalRing_eq_of_opensIso (U : S.Opens)
    (hx : s.hom (closedPoint s.residueField) ∈ U)
    (N : (geometricPointFiber B S hS s).Elements)
    (g : (SmallEtale.toScheme B S hS).obj N.1 ⟶ Scheme.Opens.toScheme (X := S) U)
    (hg : g ≫ Scheme.Opens.ι (X := S) U = B.inclusion.map N.1.obj.hom) (a : Γ(S, U)) :
    structureSheafStalkFromLocalRing B S hS s
        (S.presheaf.germ U (s.hom (closedPoint s.residueField)) hx a) =
      (colimit.ι ((CategoryOfElements.π (geometricPointFiber B S hS s)).op ⋙
        (SmallEtale.structureSheaf B S hS).obj) (op N)).hom
          (g.appTop ((Scheme.Opens.topIso (X := S) U).inv a)) := by
  let Z := zariskiNeighborhood B S hS s (s.hom (closedPoint s.residueField)) rfl ⟨U, hx⟩
  have hp : N.2.1 ≫ g = Z.2.1 := by
    apply (cancel_mono (Scheme.Opens.ι (X := S) U)).1
    rw [Category.assoc, hg]
    exact N.2.2.trans (IsOpenImmersion.lift_fac _ _ _).symm
  rw [structureSheafStalkFromLocalRing_open_germ]
  exact (colimit_ι_neighborhoodHom B S hS s N Z g hg hp
    ((Scheme.Opens.topIso (X := S) U).inv a)).symm

/-- Comparison of the étale local ring with an ind-étale algebra over an affine chart at the
image of the geometric point: if that algebra receives every augmented étale algebra uniquely,
and the ordinary local ring is a localization of the chart whose image in the étale local ring
is computed by the chart's own étale neighbourhood, then the induced isomorphism is compatible
with both canonical maps. -/
private theorem nonempty_comparison_of_indEtale (H A : Type u) [CommRing H] [CommRing A]
    [Algebra A ↥(S.presheaf.stalk (s.hom (closedPoint s.residueField)))]
    [Algebra ↥(S.presheaf.stalk (s.hom (closedPoint s.residueField))) H] [Algebra A H]
    [IsScalarTower A ↥(S.presheaf.stalk (s.hom (closedPoint s.residueField))) H]
    [Algebra A s.residueField] (p : Ideal A) [p.IsPrime]
    [IsLocalization.AtPrime ↥(S.presheaf.stalk (s.hom (closedPoint s.residueField))) p]
    (j : Spec (.of A) ⟶ S) [IsOpenImmersion j]
    (hj : Spec.map (CommRingCat.ofHom (algebraMap A s.residueField)) ≫ j = s.hom)
    (π : H →ₐ[A] s.residueField)
    (hind : (CommAlgCat.etale.{u} A).ind.{u} (CommAlgCat.of A H))
    (hlift : ∀ C : CommAlgCat.AugmentedEtale A s.residueField,
      ∃! f : C.left.obj →ₐ[A] H, π.comp f = C.hom.hom)
    (C₀ : CommAlgCat.AugmentedEtale A s.residueField)
    (hord : ∀ a : A, structureSheafStalkFromLocalRing B S hS s
        (algebraMap A ↥(S.presheaf.stalk (s.hom (closedPoint s.residueField))) a) =
      (colimit.ι ((CategoryOfElements.π (geometricPointFiber B S hS s)).op ⋙
        (SmallEtale.structureSheaf B S hS).obj)
        (op (augmentedNeighborhood B S hS s A j hj C₀))).hom
          ((Scheme.ΓSpecIso (.of C₀.left.obj)).inv (algebraMap A C₀.left.obj a))) :
    Nonempty { e : H ≃+* ↥(etaleLocalRing B S hS s) //
      (∀ r, e (algebraMap ↥(S.presheaf.stalk (s.hom (closedPoint s.residueField))) H r) =
        structureSheafStalkFromLocalRing B S hS s r) ∧
      (∀ a, structureSheafStalkToGeometricField B S hS s (e a) = π a) } := by
  set R := ↥(S.presheaf.stalk (s.hom (closedPoint s.residueField)))
  obtain ⟨e, he, hπ⟩ := exists_stalk_equiv_of_augmentedEtale B S hS s A H j hj π hind hlift
  have hbase : e.toRingHom.comp (algebraMap R H) =
      structureSheafStalkFromLocalRing B S hS s := by
    apply IsLocalization.ringHom_ext p.primeCompl
    ext a
    change e (algebraMap R H (algebraMap A R a)) =
      structureSheafStalkFromLocalRing B S hS s (algebraMap A R a)
    rw [← IsScalarTower.algebraMap_apply A R H, he C₀]
    exact (hord a).symm
  exact ⟨⟨e, RingHom.congr_fun hbase, hπ⟩⟩

/-- A geometric point factors through any affine open neighbourhood of its image, through the
map induced by the germ of the ordinary local ring at that point. -/
private theorem fromSpec_germ_stalkClosedPointTo (U : S.Opens) (hU : IsAffineOpen U)
    (hx : s.hom (closedPoint s.residueField) ∈ U) :
    Spec.map (S.presheaf.germ U (s.hom (closedPoint s.residueField)) hx ≫
        Scheme.stalkClosedPointTo s.hom) ≫ hU.fromSpec = s.hom := by
  rw [Spec.map_comp, Category.assoc]
  change Spec.map (Scheme.stalkClosedPointTo s.hom) ≫ hU.fromSpecStalk hx = s.hom
  rw [hU.fromSpecStalk_eq_fromSpecStalk hx]
  exact Scheme.Spec_stalkClosedPointTo_fromSpecStalk s.hom

/-- On an affine open neighbourhood `U` of the image of a geometric point, the germ of a section
of `U` is sent into the étale local ring as the class of that section on the étale
neighbourhood `Spec Γ(S, U)`. -/
private theorem structureSheafStalkFromLocalRing_germ_eq_augmentedNeighborhood (U : S.Opens)
    (hU : IsAffineOpen U) (hx : s.hom (closedPoint s.residueField) ∈ U)
    [Algebra Γ(S, U) s.residueField]
    (hj : Spec.map (CommRingCat.ofHom (algebraMap Γ(S, U) s.residueField)) ≫ hU.fromSpec =
      s.hom) (a : Γ(S, U)) :
    structureSheafStalkFromLocalRing B S hS s
        (S.presheaf.germ U (s.hom (closedPoint s.residueField)) hx a) =
      (colimit.ι ((CategoryOfElements.π (geometricPointFiber B S hS s)).op ⋙
        (SmallEtale.structureSheaf B S hS).obj)
        (op (augmentedNeighborhood B S hS s Γ(S, U) hU.fromSpec hj
          (CostructuredArrow.mk (Y := ⟨CommAlgCat.of Γ(S, U) Γ(S, U), inferInstance⟩)
            (CommAlgCat.ofHom (Algebra.ofId Γ(S, U) s.residueField)))))).hom
        ((Scheme.ΓSpecIso (.of Γ(S, U))).inv a) := by
  let N := augmentedNeighborhood B S hS s Γ(S, U) hU.fromSpec hj
    (CostructuredArrow.mk (Y := ⟨CommAlgCat.of Γ(S, U) Γ(S, U), inferInstance⟩)
      (CommAlgCat.ofHom (Algebra.ofId Γ(S, U) s.residueField)))
  have hf : hU.isoSpec.inv ≫ U.ι = B.inclusion.map N.1.obj.hom := by
    change hU.isoSpec.inv ≫ U.ι =
      Spec.map (CommRingCat.ofHom (algebraMap Γ(S, U) Γ(S, U))) ≫ hU.fromSpec
    rw [show CommRingCat.ofHom (algebraMap Γ(S, U) Γ(S, U)) = 𝟙 (CommRingCat.of Γ(S, U)) from rfl,
      Spec.map_id, Category.id_comp]
    exact hU.isoSpec_inv_ι
  have hv : hU.isoSpec.inv.appTop (U.topIso.inv a) = (Scheme.ΓSpecIso (.of Γ(S, U))).inv a := by
    rw [hU.isoSpec_inv_appTop]
    change (Scheme.ΓSpecIso (.of Γ(S, U))).inv (U.topIso.hom (U.topIso.inv a)) = _
    rw [Iso.inv_hom_id_apply]
  rw [structureSheafStalkFromLocalRing_eq_of_opensIso B S hS s U hx N hU.isoSpec.inv hf a]
  exact congrArg
    ((colimit.ι ((CategoryOfElements.π (geometricPointFiber B S hS s)).op ⋙
      (SmallEtale.structureSheaf B S hS).obj) (op N)).hom) hv

/-- **Stacks Project, Tag 04HX.** The étale local ring at a geometric point admits an
identification with the strict henselization of the ordinary local ring at its image, formed
with the separable closure of the ordinary residue field inside the geometric point's field,
compatible with the map from the ordinary local ring and with evaluation in that field. -/
public theorem nonempty_etaleLocalRing_strictHenselization_comparison
    (T : IsLocalRing.HenselizationTower
        (S.presheaf.stalk (s.hom (closedPoint s.residueField)))
        (separableClosure (ResidueField
          (S.presheaf.stalk (s.hom (closedPoint s.residueField)))) s.residueField)) :
    Nonempty { e : T.strictHenselization ≃+*
        ↥(etaleLocalRing B S hS s) //
      (∀ r, e (algebraMap (S.presheaf.stalk (s.hom (closedPoint s.residueField)))
        T.strictHenselization r) = structureSheafStalkFromLocalRing B S hS s r) ∧
      (∀ a, structureSheafStalkToGeometricField B S hS s (e a) =
        ((T.strictHenselizationResidueEquiv.symm
          (residue T.strictHenselization a) :
            separableClosure (ResidueField
              (S.presheaf.stalk (s.hom (closedPoint s.residueField))))
              s.residueField) : s.residueField)) } := by
  let x := s.hom (closedPoint s.residueField)
  let R := S.presheaf.stalk x
  let k := ResidueField R
  let K := s.residueField
  let L := separableClosure k K
  let H := T.strictHenselization
  let eL : L ≃+* ResidueField H := T.strictHenselizationResidueEquiv
  let : Algebra R K := ((algebraMap k K).comp (residue R)).toAlgebra
  let πR : H →ₐ[R] K :=
    { toRingHom := L.subtype.comp (eL.symm.toRingHom.comp (residue H))
      commutes' r := by
        change (eL.symm (residue H (algebraMap R H r)) : K) =
          algebraMap k K (residue R r)
        rw [← T.strictHenselizationResidueEquiv_residue r]
        change (eL.symm (eL (algebraMap k L (residue R r))) : K) = _
        rw [eL.symm_apply_apply]
        rfl }
  obtain ⟨U, hU, hx, -⟩ := exists_isAffineOpen_mem_and_subset
    (X := S) (x := x) (U := ⊤) (by trivial)
  let A := Γ(S, U)
  let : Algebra A R := TopCat.Presheaf.algebra_section_stalk S.presheaf ⟨x, hx⟩
  let : Algebra A k := ((residue R).comp (algebraMap A R)).toAlgebra
  let : Algebra A H := ((algebraMap R H).comp (algebraMap A R)).toAlgebra
  let : Algebra A K := ((algebraMap R K).comp (algebraMap A R)).toAlgebra
  have : IsScalarTower A R H := .of_algebraMap_eq fun _ => rfl
  have : IsScalarTower A R K := .of_algebraMap_eq fun _ => rfl
  have : IsScalarTower A k K := .of_algebraMap_eq fun _ => rfl
  let p := (hU.primeIdealOf ⟨x, hx⟩).asIdeal
  have : IsLocalization.AtPrime R p := hU.isLocalization_stalk ⟨x, hx⟩
  let j : Spec (.of A) ⟶ S := hU.fromSpec
  have hRK : CommRingCat.ofHom (algebraMap R K) = Scheme.stalkClosedPointTo s.hom :=
    S.residue_descResidueField (Scheme.stalkClosedPointTo s.hom)
  have hj : Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫ j = s.hom := by
    have hh : CommRingCat.ofHom (algebraMap A K) =
        S.presheaf.germ U x hx ≫ Scheme.stalkClosedPointTo s.hom := by
      rw [← hRK]
      rfl
    rw [hh]
    exact fromSpec_germ_stalkClosedPointTo S s U hU hx
  let π : H →ₐ[A] K := πR.restrictScalars A
  let C₀ : CommAlgCat.AugmentedEtale A K :=
    CostructuredArrow.mk (Y := ⟨CommAlgCat.of A A, inferInstance⟩)
      (CommAlgCat.ofHom (Algebra.ofId A K))
  exact nonempty_comparison_of_indEtale B S hS s H A p j hj π
    (CommAlgCat.ind_etale_comp (CommAlgCat.ind_etale_atPrime A R p)
      (IsHenselization.ind_etale_of_universe_le L))
    (existsUnique_lift_augmentedEtale eL π (fun _ => rfl)) C₀
    (structureSheafStalkFromLocalRing_germ_eq_augmentedNeighborhood B S hS s U hU hx hj)

end AlgebraicGeometry

end
