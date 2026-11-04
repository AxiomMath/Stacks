module

public import StacksFrontier.AlgebraicGeometry.Quot.CurvesGrc1H01
public import StacksFrontier.AlgebraicGeometry.Spaces.DescentLocus.ClopenGlobalFunction
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Fibres.RestrictedFibreProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Fibres.RestrictedFibreRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperFlatGlobalFunctionsDVR
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperGeometricallyConnectedGlobalFunctions

/-!
# Connected geometric fibres spread from the closed point of a discrete valuation ring

Let `f : X ⟶ Y` be a proper, flat morphism of finite presentation of algebraic spaces, and let
`Spec V ⟶ Y` be a morphism from the spectrum of a discrete valuation ring `V`. If the fibre of
`f` over the closed point of `Spec V` is geometrically reduced and geometrically connected —
its geometric fibre has exactly one connected component (Stacks 0E1B) — then the geometric
fibre of `f` over the generic point of `Spec V` is connected as well.

Indeed the base change `X_V` of `f` to `Spec V` is proper, flat and of finite presentation over
`V` with closed fibre `X_k` proper, geometrically reduced and geometrically connected over `k`,
so `k = H⁰(X_k, 𝒪)` (Stacks 0DMY); by
`AlgebraicGeometry.Space.bijective_algebraMap_globalFunctions_relocalizeRestrict_of_dvr` the
global functions of the base change of `X_V` to an algebraically closed field `K` flat over `V`
are `K`, so that base change has no nontrivial idempotent global function and is connected.

## Main results

* `AlgebraicGeometry.Space.connectedPoints_of_bijective_algebraMap_globalFunctions`: an algebraic
  space over a field `k` with `k = H⁰(X, 𝒪)` is connected.
* `AlgebraicGeometry.Space.isGeometricallyConnected_fibreOverFieldValuedPoint_of_eq_one`: the
  fibre over a field-valued point of a point with connected geometric fibre is geometrically
  connected.
* `AlgebraicGeometry.Space.numberGeometricConnectedComponents_eq_one_of_dvr`: the statement
  above.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite IsLocalRing

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/-- The support of the zero global function is empty. -/
private theorem sectionSupport_zero {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :
    sectionSupport B S hS F 0 = ∅ := by
  ext x
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨U, p, hp, -⟩
  change pointsToScheme B S hS U.obj.left p ∈
    ((BigFppfOver.toScheme B S hS).obj U.obj.left).basicOpen
      (0 : Γ((BigFppfOver.toScheme B S hS).obj U.obj.left, ⊤)) at hp
  rwa [Scheme.basicOpen_zero] at hp

/-- **An algebraic space with constant global functions is connected.** Let `X` be an algebraic
space over a field `k` with `k = H⁰(X, 𝒪)`. Then `|X|` is connected: it is nonempty since its
ring of global functions is nonzero, and a clopen subset `T` of `|X|` is the support of an
idempotent global function, which is `0` or `1`. -/
theorem connectedPoints_of_bijective_algebraMap_globalFunctions (B : BigFppfSite.{u})
    (k : Type u) [Field k] (hk : B.Contains (Spec (.of k)))
    (X : (BigFppfOver B (Spec (.of k)) hk)ᵒᵖ ⥤ Type u)
    (hX : IsAlgebraicSpace B (Spec (.of k)) hk X)
    (h : Function.Bijective (algebraMap k (globalFunctions B (Spec (.of k)) hk X))) :
    ConnectedPoints B (Spec (.of k)) hk X := by
  let e := RingEquiv.ofBijective (algebraMap k (globalFunctions B (Spec (.of k)) hk X)) h
  have : Nontrivial (globalFunctions B (Spec (.of k)) hk X) := e.symm.toEquiv.nontrivial
  have hne := nonempty_points_of_nontrivial_globalFunctions (B := B) (S := Spec (.of k))
    (hS := hk) (F := X)
  -- an idempotent global function is `0` or `1`
  have hidem : ∀ s : globalFunctions B (Spec (.of k)) hk X, IsIdempotentElem s → s = 0 ∨ s = 1 :=
    fun s hs => (IsIdempotentElem.iff_eq_zero_or_one.mp (hs.map e.symm)).imp
      (fun h0 => e.symm.injective (h0.trans (map_zero e.symm).symm))
      (fun h1 => e.symm.injective (h1.trans (map_one e.symm).symm))
  rw [ConnectedPoints, connectedSpace_iff_clopen]
  refine ⟨hne, fun T hT => ?_⟩
  have hsupp := sectionSupport_clopenGlobalFunction hX hT
  have hsuppc := sectionSupport_clopenGlobalFunction hX hT.compl
  rcases hidem _ (isIdempotentElem_clopenGlobalFunction hT) with h0 | h1
  · left
    rw [← hsupp, h0, sectionSupport_zero]
  · rcases hidem _ (isIdempotentElem_clopenGlobalFunction hT.compl) with h0' | h1'
    · right
      rw [← compl_compl T, ← hsuppc, h0', sectionSupport_zero, Set.compl_empty]
    · exfalso
      obtain ⟨x⟩ := hne
      exact iff_not_self (Set.ext_iff.mp (hsupp.symm.trans
        ((congrArg (sectionSupport B _ hk X) (h1.trans h1'.symm)).trans hsuppc)) x)

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- For a point with algebraically closed residue field, the fibre has one geometric connected
component at its class exactly when the points of the fibre over the field are connected. -/
private theorem numberGeometricConnectedComponents_class_eq_one_iff
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (q : FieldValuedPoint B S hS Y) [IsAlgClosed q.carrier] :
    numberGeometricConnectedComponents B S hS f (q.class B S hS Y) = 1 ↔
      ConnectedSpace (points B (Spec (.of q.carrier)) q.contained (fiberOverField B S hS f q)) := by
  have h := numberGeometricConnectedComponents_eq B S hS hX hY f
    (⟨q, inferInstance⟩ : GeometricPoint B S hS Y)
  change numberGeometricConnectedComponents B S hS f (q.class B S hS Y) = _ at h
  rw [h, geometricFiberComponentCount_eq_overField B S hS hX hY f q, Cardinal.toENat_eq_one]
  exact (connectedSpace_iff_cardinalMk_connectedComponents_eq_one _).symm

/-- **The fibre over a field-valued point is geometrically connected when the geometric fibre at
its point is connected.** If the geometric fibre of `f : X ⟶ Y` at the point of `|Y|` represented
by a field-valued point `p` has exactly one connected component (Stacks 0E1B), then the fibre
`X_k` over `p` is geometrically connected over `k` (Stacks 0A0Z): over an algebraic closure `K`
of `k` its base change is the fibre over the geometric point `Spec K ⟶ Spec k ⟶ Y`, which lies
over the same point of `|Y|`. -/
theorem isGeometricallyConnected_fibreOverFieldValuedPoint_of_eq_one (f : X ⟶ Y)
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (p : FieldValuedPoint B S hS Y)
    (h : numberGeometricConnectedComponents B S hS f (p.class B S hS Y) = 1) :
    IsGeometricallyConnected B p.carrier p.contained (fibreOverFieldValuedPoint B S hS f p) := by
  let K := AlgebraicClosure p.carrier
  have hK : B.Contains (Spec (.of K)) := B.contains_spec_algebraicClosure p.contained
  let g : B.obj hK ⟶ B.obj p.contained := fieldExtensionMap B p.carrier K p.contained hK
  let q : FieldValuedPoint B S hS Y :=
    { carrier := K
      contained := hK
      toBase := (g ≫ (⟨p.toBase⟩ : B.obj p.contained ⟶ B.obj hS)).hom
      value := Y.map (Over.homMk g rfl : Over.mk (g ≫ (⟨p.toBase⟩ : B.obj p.contained ⟶
        B.obj hS)) ⟶ p.siteObject).op p.value }
  have hqp : q.class B S hS Y = p.class B S hS Y :=
    FieldValuedPoint.class_eq_class_of_hasCommonExtension B S hS Y
      ⟨q, FieldValuedPoint.dominates_refl B S hS Y q, ⟨Over.homMk g rfl, rfl⟩⟩
  have hXp : IsAlgebraicSpace B (Spec (.of p.carrier)) p.contained
      (fiberOverField B S hS f p) := fiberOverField_isAlgebraicSpace B S hS hX hY f p
  change IsGeometricallyConnected B p.carrier p.contained (fiberOverField B S hS f p)
  rw [isGeometricallyConnected_iff_relocalizeRestrict B p.carrier K p.contained hK _ hXp,
    isGeometricallyConnected_iff_connectedSpace_of_isSepClosed B K hK _
      (isAlgebraicSpace_relocalizeRestrict B (Spec (.of K)) (Spec (.of p.carrier)) hK
        p.contained g _ hXp)]
  exact connectedSpace_points_of_iso B (Spec (.of K)) hK
    (fiberOverFieldBaseChangeIso B S hS f p q g rfl rfl).symm
    ((numberGeometricConnectedComponents_class_eq_one_iff B S hS hX hY f q).mp (by rwa [hqp]))

/-- **Connected geometric fibres spread from the closed point of a discrete valuation ring.** Let
`f : X ⟶ Y` be a proper, flat morphism of finite presentation of algebraic spaces over `S`, let
`V` be a discrete valuation ring and `v` a point of `Y` with values in `Spec V`, lying over
`g : Spec V ⟶ S`. Let `p_s` be the induced point of `Y` with values in the residue field of `V`,
and `p_K` the induced point with values in an algebraically closed field `K` flat over `V` (for
instance an algebraic closure of the fraction field). If the fibre of `f` at the point of `p_s`
is geometrically reduced and its geometric fibre is connected, then the geometric fibre of `f`
at the point of `p_K` is connected. -/
theorem numberGeometricConnectedComponents_eq_one_of_dvr (f : X ⟶ Y)
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hf : IsProper B S hS f) (hfl : IsFlat B S hS f) (hfp : IsFinitePresentation B S hS f)
    {V : Type u} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    (hV : B.Contains (Spec (.of V))) (g : B.obj hV ⟶ B.obj hS) (v : Y.obj (op (Over.mk g)))
    (hP : B.Contains (Spec (.of (maximalIdeal V).ResidueField))) (gP : B.obj hP ⟶ B.obj hV)
    (hgP : B.inclusion.map gP =
      Spec.map (CommRingCat.ofHom (algebraMap V (maximalIdeal V).ResidueField)))
    (K : Type u) [Field K] [IsAlgClosed K] [Algebra V K] [Module.Flat V K]
    (hK : B.Contains (Spec (.of K))) (gK : B.obj hK ⟶ B.obj hV)
    (hgK : B.inclusion.map gK = Spec.map (CommRingCat.ofHom (algebraMap V K)))
    (hred : IsGeometricallyReducedFibreAt B S hS f hX hY
      (FieldValuedPoint.class B S hS Y
        { carrier := (maximalIdeal V).ResidueField, contained := hP, toBase := (gP ≫ g).hom,
          value := Y.map (Over.homMk gP rfl).op v }))
    (h1 : numberGeometricConnectedComponents B S hS f
      (FieldValuedPoint.class B S hS Y
        { carrier := (maximalIdeal V).ResidueField, contained := hP, toBase := (gP ≫ g).hom,
          value := Y.map (Over.homMk gP rfl).op v }) = 1) :
    numberGeometricConnectedComponents B S hS f
      (FieldValuedPoint.class B S hS Y
        { carrier := K, contained := hK, toBase := (gK ≫ g).hom,
          value := Y.map (Over.homMk gK rfl).op v }) = 1 := by
  let ps : FieldValuedPoint B S hS Y :=
    { carrier := (maximalIdeal V).ResidueField, contained := hP, toBase := (gP ≫ g).hom,
      value := Y.map (Over.homMk gP rfl).op v }
  let pK : FieldValuedPoint B S hS Y :=
    { carrier := K, contained := hK, toBase := (gK ≫ g).hom,
      value := Y.map (Over.homMk gK rfl).op v }
  have hF := isAlgebraicSpace_restrictedFibre B S hS f hX hY hV g v
  -- the closed fibre has constant global functions (Stacks 0DMY)
  have hs : Function.Bijective (algebraMap ps.carrier (globalFunctions B
      (Spec (.of ps.carrier)) ps.contained (fibreOverFieldValuedPoint B S hS f ps))) :=
    bijective_algebraMap_globalFunctions_of_isGeometricallyReduced B ps.carrier ps.contained _
      (isAlgebraicSpace_fibreOverFieldValuedPoint B S hS f hX hY ps) _
      (isProper_toYonedaId_fibreOverFieldValuedPoint B S hS f hX hY hf ps)
      (isGeometricallyReduced_fibreOverFieldValuedPoint B S hS f hX hY ps hred)
      (isGeometricallyConnected_fibreOverFieldValuedPoint_of_eq_one B S hS f hX hY ps h1)
  have hs' : ∀ (hP' : B.Contains (Spec (.of (maximalIdeal V).ResidueField)))
      (gP' : B.obj hP' ⟶ B.obj hV),
      B.inclusion.map gP' =
        Spec.map (CommRingCat.ofHom (algebraMap V (maximalIdeal V).ResidueField)) →
      Function.Bijective (algebraMap (maximalIdeal V).ResidueField (globalFunctions B
        (Spec (.of (maximalIdeal V).ResidueField)) hP'
          ((OverShriek.relocalizeRestrict gP').obj (restrictedFibre B S hS f hV g v)))) := by
    intro hP' gP' hgP'
    obtain rfl : hP' = hP := rfl
    obtain rfl : gP' = gP := B.inclusion.map_injective (hgP'.trans hgP.symm)
    exact (bijective_algebraMap_globalFunctions_congr B
      (isAlgebraicSpace_fibreOverFieldValuedPoint B S hS f hX hY ps)
      (isAlgebraicSpace_relocalizeRestrict B _ _ hP' hV gP' _ hF)
      (nonempty_restrictedFibre_iso_relocalizeRestrict B S hS f hV hP' g gP' v).some).mp hs
  -- hence so does the fibre over `K`
  have hKf : Function.Bijective (algebraMap pK.carrier (globalFunctions B
      (Spec (.of pK.carrier)) pK.contained (fibreOverFieldValuedPoint B S hS f pK))) :=
    (bijective_algebraMap_globalFunctions_congr B
      (isAlgebraicSpace_fibreOverFieldValuedPoint B S hS f hX hY pK)
      (isAlgebraicSpace_relocalizeRestrict B _ _ hK hV gK _ hF)
      (nonempty_restrictedFibre_iso_relocalizeRestrict B S hS f hV hK g gK v).some).mpr
      (bijective_algebraMap_globalFunctions_relocalizeRestrict_of_dvr B hF _
        (isProper_restrictedFibre B S hS f hV g v hX hY hf)
        (isFlat_restrictedFibre B S hS f hV g v hX hY hfl)
        (isFinitePresentation_restrictedFibre B S hS f hV g v hX hY hfp) hs' K hK gK hgK)
  exact (numberGeometricConnectedComponents_class_eq_one_iff B S hS hX hY f pK).mpr
    (connectedPoints_of_bijective_algebraMap_globalFunctions B K hK _
      (isAlgebraicSpace_fibreOverFieldValuedPoint B S hS f hX hY pK) hKf)

end AlgebraicGeometry.Space
