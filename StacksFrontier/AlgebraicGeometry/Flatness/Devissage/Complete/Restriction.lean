module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Flatness.Devissage.Complete.Transport
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.NonemptyOpen

/-!
# Restricting a one-step dévissage to standard opens

Given a one-step dévissage of `F/X/S` at `x` and standard opens of the four schemes which
contain the four distinguished points, are compatible with the three morphisms, and whose
smooth part surjects onto the base part, the canonical restrictions of all the data form
again a one-step dévissage at `x`: a standard shrinking in the sense of Stacks 05H9. Such
opens exist with a prescribed standard open of the smooth scheme, provided one is allowed to
shrink the base, and then the closed part can be taken cartesian over the smooth and the
source parts.

## Main definitions

* `AlgebraicGeometry.OneStepDevissageAt.standardShrinkingOfOpens`: the standard shrinking
  attached to a compatible choice of standard opens.

## Main results

* `AlgebraicGeometry.OneStepDevissageAt.exists_standardShrinking_cartesian_of_basicOpen`: a
  prescribed standard open of the smooth scheme is realized, after shrinking the base, by a
  standard shrinking whose closed part is cartesian over both the smooth and the source part.
* `AlgebraicGeometry.purelyTranscendental_of_ringEquiv`: pure transcendence transports along
  a pair of compatible ring isomorphisms of the base field and of the extension.

## Implementation notes

The base open is shrunk to a basic open inside the image of the prescribed open of the smooth
scheme, which is open because a smooth morphism is open; that is what makes the restricted
structure morphism surjective, hence its fibres nonempty, hence of the same dimension as the
fibres of the original one by Stacks 0A21.

The dimension conditions are checked through explicit homeomorphisms: the support of the
module on a fibre is homeomorphic to the set of points of the source lying over the base
point and in the support, and restricting to an open subscheme intersects that set with the
open. The local dimension at a point is unchanged by an open embedding, and the total
dimension is unchanged because the point realizing the maximum is in the open.

## References

* [Stacks Project, Tag 05H9](https://stacks.math.columbia.edu/tag/05H9)
* [Stacks Project, Tag 0A21](https://stacks.math.columbia.edu/tag/0A21)
* [Stacks Project, Tag 030E](https://stacks.math.columbia.edu/tag/030E)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-! ### Restriction of morphisms and modules to opens -/

section ResLE

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- The square exhibiting the restriction of a morphism to the inverse image of an open is
cartesian.

This is the orientation with the two open immersions as the horizontal legs;
`AlgebraicGeometry.isPullback_resLE` is the same square with the roles of the legs
exchanged. -/
lemma isPullback_resLE' (V : S.Opens) (U : X.Opens) (hU : U = f ⁻¹ᵁ V) :
    IsPullback U.ι (f.resLE V U hU.le) f V.ι := by
  subst U
  simpa only [Scheme.Hom.resLE_eq_morphismRestrict] using (isPullback_morphismRestrict f V).flip

/-- A surjective restriction of a morphism with geometrically irreducible fibres again has
geometrically irreducible fibres. -/
lemma geometricallyIrreducible_resLE [GeometricallyIrreducible f] (V : S.Opens) (U : X.Opens)
    (hUV : U ≤ f ⁻¹ᵁ V) [Surjective (f.resLE V U hUV)] :
    GeometricallyIrreducible (f.resLE V U hUV) := by
  have : GeometricallyIrreducible (f ∣_ V) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (isPullback_morphismRestrict f V).flip inferInstance
  have : Surjective (X.homOfLE hUV ≫ f ∣_ V) := ‹Surjective (f.resLE V U hUV)›
  show GeometricallyIrreducible (X.homOfLE hUV ≫ f ∣_ V)
  infer_instance

end ResLE

section Restrict

variable {X : Scheme.{u}} (F : X.Modules) (U : X.Opens)

/-- The restriction of a quasi-coherent module to an open is quasi-coherent. -/
lemma isQuasicoherent_restrict [F.IsQuasicoherent] : (F.restrict U.ι).IsQuasicoherent :=
  inferInstanceAs ((Scheme.Modules.restrictFunctor U.ι).obj F).IsQuasicoherent

/-- The restriction of a module of finite type to an open is of finite type.

This is the special case of `AlgebraicGeometry.isFiniteType_restrict`, which allows an
arbitrary open immersion in place of the inclusion of an open. -/
lemma isFiniteType_restrict' [F.IsFiniteType] : (F.restrict U.ι).IsFiniteType :=
  SheafOfModules.isFiniteType_of_iso
    ((Scheme.Modules.restrictFunctorIsoPullback U.ι).app F).symm
    (SheafOfModules.pullback_isFiniteType U.ι.toLRSHom.toShHom F)

/-- The support of the restriction of a module of finite type to an open is the part of its
support lying in that open. -/
lemma supp_restrict [F.IsFiniteType] :
    SheafOfModules.supp (F.restrict U.ι) = U.ι ⁻¹' SheafOfModules.supp F := by
  ext p
  rw [SheafOfModules.mem_supp_iff_of_iso
    ((Scheme.Modules.restrictFunctorIsoPullback U.ι).app F) p, Stacks.Modules.supp_pullback]

/-- The direct image along an affine morphism commutes with restriction to an open of the
target and its full inverse image. -/
def restrictPushforwardIso {Z : Scheme.{u}} (i : Z ⟶ X) [IsAffineHom i] (G : Z.Modules)
    [G.IsQuasicoherent] (X' : X.Opens) (Z' : Z.Opens) (hZ : Z' = i ⁻¹ᵁ X') :
    (Scheme.Modules.pullback X'.ι).obj ((Scheme.Modules.pushforward i).obj G) ≅
      (Scheme.Modules.pushforward (i.resLE X' Z' (by rw [hZ]))).obj (G.restrict Z'.ι) := by
  subst Z'
  have hsq : IsPullback (i ⁻¹ᵁ X').ι (i.resLE X' (i ⁻¹ᵁ X') le_rfl) i X'.ι :=
    isPullback_resLE' i X' (i ⁻¹ᵁ X') rfl
  have : IsIso ((AffinePushforward.baseChangeNatTrans hsq.w).app G) :=
    AffineBaseChangeIso.isIso_baseChangeNatTrans_of_isAffineHom hsq G
  exact asIso ((AffinePushforward.baseChangeNatTrans hsq.w).app G) ≪≫
    (Scheme.Modules.pushforward (i.resLE X' (i ⁻¹ᵁ X') le_rfl)).mapIso
      ((Scheme.Modules.restrictFunctorIsoPullback (i ⁻¹ᵁ X').ι).app G).symm

end Restrict

/-! ### Fibres, supports and dimension under restriction -/

/-- The support of the module on a fibre is the set of points of the source lying over the
base point and in the support of the module. -/
def fiberSupportHomeo {X S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules) [F.IsFiniteType]
    (s : S) :
    SheafOfModules.supp ((Scheme.Modules.pullback (f.fiberι s)).obj F) ≃ₜ
      {p : X // f p = s ∧ p ∈ SheafOfModules.supp F} where
  toFun p := ⟨f.fiberι s p, (f.fiberHomeo s p).property, by
    simpa only [Stacks.Modules.supp_pullback, Set.mem_preimage] using p.property⟩
  invFun p := ⟨(f.fiberHomeo s).symm ⟨p, p.property.1⟩, by
    rw [Stacks.Modules.supp_pullback]
    simpa using p.property.2⟩
  left_inv p := Subtype.ext ((f.fiberHomeo s).symm_apply_apply p.val)
  right_inv p := Subtype.ext (f.fiberι_fiberHomeo_symm s _)
  continuous_toFun := ((f.fiberι s).continuous.comp continuous_subtype_val).subtype_mk _
  continuous_invFun :=
    ((f.fiberHomeo s).symm.continuous.comp (continuous_subtype_val.subtype_mk _)).subtype_mk _

/-- If a point of an open embedding's source has maximal local dimension in the target, then
the two spaces have the same dimension and the point has maximal local dimension in the
source. -/
lemma dim_eq_of_isOpenEmbedding {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    {j : A → B} (hj : Topology.IsOpenEmbedding j) (a : A)
    (hd : topologicalKrullDimAt B (j a) = topologicalKrullDim B) :
    topologicalKrullDim A = topologicalKrullDim B ∧
      topologicalKrullDimAt A a = topologicalKrullDim A := by
  have hle : topologicalKrullDimAt A a ≤ topologicalKrullDim A := by
    refine (topologicalKrullDimAt_isLeast A a).2 ⟨Set.univ, Set.mem_univ _, isOpen_univ, ?_⟩
    exact (IsHomeomorph.topologicalKrullDim_eq _ (Homeomorph.Set.univ A).isHomeomorph).symm
  have he := hj.topologicalKrullDimAt_eq a
  have hg := le_antisymm hj.isEmbedding.isInducing.topologicalKrullDim_le
    ((hd.symm.trans he).le.trans hle)
  exact ⟨hg, he.symm.trans (hd.trans hg.symm)⟩

/-- The two descriptions of the points of a restricted fibre lying in the support agree. -/
def restrictedSupportHomeo {X S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules) [F.IsFiniteType]
    (V : S.Opens) (U : X.Opens) (hUV : U ≤ f ⁻¹ᵁ V) [(F.restrict U.ι).IsFiniteType] (s : V) :
    {p : U.toScheme // f.resLE V U hUV p = s ∧
        p ∈ SheafOfModules.supp (F.restrict U.ι)} ≃ₜ
      {p : U.toScheme // f p.val = s.val ∧ p.val ∈ SheafOfModules.supp F} :=
  Homeomorph.setCongr (by
    ext p
    change ((f.resLE V U hUV) p = s ∧ p ∈ SheafOfModules.supp (F.restrict U.ι)) ↔
      (f p.val = s.val ∧ p.val ∈ SheafOfModules.supp F)
    rw [supp_restrict F U]
    exact ⟨fun h ↦
        ⟨(Scheme.Hom.coe_resLE_apply f hUV p).symm.trans (congrArg Subtype.val h.1), h.2⟩,
      fun h ↦ ⟨Subtype.ext ((Scheme.Hom.coe_resLE_apply f hUV p).trans h.1), h.2⟩⟩)

/-- Restricting to an open containing a point of maximal local dimension in the support on
its fibre keeps both the dimension of that support and the maximality at the point. -/
lemma restrictedSupportDimension {X S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules)
    [F.IsFiniteType] (V : S.Opens) (U : X.Opens) (hUV : U ≤ f ⁻¹ᵁ V)
    [(F.restrict U.ι).IsFiniteType] (x : X) (hx : x ∈ U)
    (hm : f.asFiber x ∈
      SheafOfModules.supp ((Scheme.Modules.pullback (f.fiberι (f x))).obj F))
    (hd : topologicalKrullDimAt
        (SheafOfModules.supp ((Scheme.Modules.pullback (f.fiberι (f x))).obj F))
        ⟨f.asFiber x, hm⟩ =
      topologicalKrullDim
        (SheafOfModules.supp ((Scheme.Modules.pullback (f.fiberι (f x))).obj F)))
    (hm' : (f.resLE V U hUV).asFiber ⟨x, hx⟩ ∈ SheafOfModules.supp
      ((Scheme.Modules.pullback ((f.resLE V U hUV).fiberι
        ((f.resLE V U hUV) ⟨x, hx⟩))).obj (F.restrict U.ι))) :
    topologicalKrullDim (SheafOfModules.supp
        ((Scheme.Modules.pullback ((f.resLE V U hUV).fiberι
          ((f.resLE V U hUV) ⟨x, hx⟩))).obj (F.restrict U.ι))) =
      topologicalKrullDim
        (SheafOfModules.supp ((Scheme.Modules.pullback (f.fiberι (f x))).obj F)) ∧
    topologicalKrullDimAt (SheafOfModules.supp
        ((Scheme.Modules.pullback ((f.resLE V U hUV).fiberι
          ((f.resLE V U hUV) ⟨x, hx⟩))).obj (F.restrict U.ι)))
        ⟨(f.resLE V U hUV).asFiber ⟨x, hx⟩, hm'⟩ =
      topologicalKrullDim (SheafOfModules.supp
        ((Scheme.Modules.pullback ((f.resLE V U hUV).fiberι
          ((f.resLE V U hUV) ⟨x, hx⟩))).obj (F.restrict U.ι))) := by
  have hs : ((f.resLE V U hUV) ⟨x, hx⟩).val = f x := Scheme.Hom.coe_resLE_apply _ _ _
  set P : Set X := {p | f p = f x ∧ p ∈ SheafOfModules.supp F} with hP
  set e := fiberSupportHomeo f F (f x) with he
  set e' := (fiberSupportHomeo (f.resLE V U hUV) (F.restrict U.ι)
    ((f.resLE V U hUV) ⟨x, hx⟩)).trans
      (restrictedSupportHomeo f F V U hUV ((f.resLE V U hUV) ⟨x, hx⟩)) with he'
  set e'' : {p : U.toScheme // f p.val = ((f.resLE V U hUV) ⟨x, hx⟩).val ∧
      p.val ∈ SheafOfModules.supp F} ≃ₜ (U.ι ⁻¹' P) :=
    Homeomorph.setCongr (by
      ext p
      show (f p.val = ((f.resLE V U hUV) ⟨x, hx⟩).val ∧ _) ↔ (f p.val = f x ∧ _)
      rw [hs]
      rfl) with he''
  have hj : Topology.IsOpenEmbedding (e.symm ∘ P.restrictPreimage U.ι ∘ e'' ∘ e') :=
    e.symm.isOpenEmbedding.comp
      ((U.ι.isOpenEmbedding.restrictPreimage P).comp
        (e''.isOpenEmbedding.comp e'.isOpenEmbedding))
  refine dim_eq_of_isOpenEmbedding hj ⟨(f.resLE V U hUV).asFiber ⟨x, hx⟩, hm'⟩ ?_
  have hpoint : (e.symm ∘ P.restrictPreimage U.ι ∘ e'' ∘ e')
      ⟨(f.resLE V U hUV).asFiber ⟨x, hx⟩, hm'⟩ = ⟨f.asFiber x, hm⟩ := by
    apply Subtype.ext
    apply (f.fiberι (f x)).isEmbedding.injective
    show f.fiberι (f x) ((f.fiberHomeo (f x)).symm _) = _
    rw [Scheme.Hom.fiberι_fiberHomeo_symm]
    show U.ι ((f.resLE V U hUV).fiberι ((f.resLE V U hUV) ⟨x, hx⟩)
      ((f.resLE V U hUV).asFiber ⟨x, hx⟩)) = _
    refine Eq.trans (congrArg (fun p : U.toScheme ↦ U.ι p)
      ((f.resLE V U hUV).fiberι_asFiber ⟨x, hx⟩)) ?_
    exact (f.fiberι_asFiber x).symm
  rwa [hpoint]

/-- The points of a restricted fibre are the points of the original fibre lying in the open
subscheme. -/
def restrictedFiberHomeo {X S : Scheme.{u}} (f : X ⟶ S) (V : S.Opens) (U : X.Opens)
    (hUV : U ≤ f ⁻¹ᵁ V) (s : V.toScheme) :
    (f.resLE V U hUV).fiber s ≃ₜ {p : f.fiber s.val // f.fiberι s.val p ∈ U} where
  toFun p := ⟨(f.fiberHomeo s.val).symm
    ⟨((f.resLE V U hUV).fiberι s p).val, by
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      exact (Scheme.Hom.coe_resLE_apply f hUV ((f.resLE V U hUV).fiberι s p)).symm.trans
        (congrArg Subtype.val ((f.resLE V U hUV).fiberHomeo s p).property)⟩, by
    simpa only [Scheme.Hom.fiberι_fiberHomeo_symm] using
      ((f.resLE V U hUV).fiberι s p).2⟩
  invFun p := ((f.resLE V U hUV).fiberHomeo s).symm
    ⟨⟨f.fiberι s.val p, p.property⟩, by
      apply Subtype.ext
      simpa only [Scheme.Hom.coe_resLE_apply, Scheme.Hom.fiberHomeo_apply, Set.mem_preimage,
        Set.mem_singleton_iff] using (f.fiberHomeo s.val p).property⟩
  left_inv p := by
    apply ((f.resLE V U hUV).fiberι s).isEmbedding.injective
    simp only [Scheme.Hom.fiberι_fiberHomeo_symm]
    rfl
  right_inv p := by
    apply Subtype.ext
    apply (f.fiberι s.val).isEmbedding.injective
    simp only [Scheme.Hom.fiberι_fiberHomeo_symm]
  continuous_toFun := Continuous.subtype_mk ((f.fiberHomeo s.val).symm.continuous.comp
    ((continuous_subtype_val.comp ((f.resLE V U hUV).fiberι s).continuous).subtype_mk _)) _
  continuous_invFun := ((f.resLE V U hUV).fiberHomeo s).symm.continuous.comp
    ((((f.fiberι s.val).continuous.comp continuous_subtype_val).subtype_mk _).subtype_mk _)

/-- A nonempty open part of a fibre of a morphism locally of finite type with geometrically
irreducible fibres has the dimension of the whole fibre. -/
lemma restrictedFiberDimension {X S : Scheme.{u}} (g : X ⟶ S) [LocallyOfFiniteType g]
    [GeometricallyIrreducible g] (V : S.Opens) (U : X.Opens) (hUV : U ≤ g ⁻¹ᵁ V)
    [Surjective (g.resLE V U hUV)] (s : V.toScheme) :
    topologicalKrullDim ((g.resLE V U hUV).fiber s) = topologicalKrullDim (g.fiber s.val) := by
  have : LocallyOfFiniteType (g.fiberToSpecResidueField s.val) :=
    inferInstanceAs (LocallyOfFiniteType (Limits.pullback.snd _ _))
  have hne : Nonempty ((g.resLE V U hUV).fiber s) := by
    rw [((g.resLE V U hUV).fiberHomeo s).nonempty_congr]
    obtain ⟨p, hp⟩ := (g.resLE V U hUV).surjective s
    exact ⟨p, hp⟩
  refine (IsHomeomorph.topologicalKrullDim_eq _
    (restrictedFiberHomeo g V U hUV s).isHomeomorph).trans ?_
  symm
  refine topologicalKrullDim_eq_of_isOpen (S.residueField s.val) (g.fiber s.val)
    (g.fiberToSpecResidueField s.val) (g.fiberι s.val ⁻¹' (U : Set X))
    (U.isOpen.preimage (g.fiberι s.val).continuous) ?_
  exact Set.nonempty_coe_sort.mp ((restrictedFiberHomeo g V U hUV s).nonempty_congr.mp hne)

/-! ### Pure transcendence under a change of fields -/

/-- Pure transcendence transports along a pair of compatible ring isomorphisms of the base
field and of the extension. -/
@[stacks 030E "3, a part of the correctness"]
lemma purelyTranscendental_of_ringEquiv {k K k' K' : Type*} [Field k] [Field K] [Field k']
    [Field K'] [Algebra k K] [Algebra k' K'] (e : k ≃+* k') (E : K ≃+* K')
    (hc : (algebraMap k' K').comp e = E.toRingHom.comp (algebraMap k K))
    [PurelyTranscendental k K] : PurelyTranscendental k' K' := by
  obtain ⟨s, hi, hs⟩ := PurelyTranscendental.exists_basis k K
  refine PurelyTranscendental.of_algebraicIndependent
    (hi.ringHom_of_comp_eq e E e.surjective E.injective hc) ?_
  have hle : (IntermediateField.adjoin k s).toSubfield ≤
      (IntermediateField.adjoin k' (Set.range (E ∘ (Subtype.val : s → K)))).toSubfield.comap
        E.toRingHom := by
    refine IntermediateField.adjoin_le_subfield _ _ ?_ ?_
    · rintro _ ⟨a, rfl⟩
      show E (algebraMap k K a) ∈
        IntermediateField.adjoin k' (Set.range (E ∘ (Subtype.val : s → K)))
      have hc' : algebraMap k' K' (e a) = E (algebraMap k K a) := RingHom.congr_fun hc a
      rw [← hc']
      exact IntermediateField.algebraMap_mem _ _
    · intro a ha
      exact IntermediateField.subset_adjoin _ _ ⟨⟨a, ha⟩, rfl⟩
  refine top_le_iff.mp fun a _ => ?_
  obtain ⟨b, rfl⟩ := E.surjective a
  exact hle (hs ▸ trivial)

/-- The residue field at a point of an open subscheme is the residue field at that point,
compatibly with the residue field of the base: pure transcendence of a residue field
extension survives restriction to opens.

This states the hypothesis on the base point with the subtype projection `x.val`;
`AlgebraicGeometry.purelyTranscendental_resLE` is the same statement written with the open
immersion `U.ι x` instead. -/
lemma purelyTranscendental_resLE' {X S : Scheme.{u}} (f : X ⟶ S) (V : S.Opens) (U : X.Opens)
    (hUV : U ≤ f ⁻¹ᵁ V) (x : U.toScheme) (s : S) (hs : f x.val = s) (s' : V.toScheme)
    (hs' : (f.resLE V U hUV) x = s')
    (H : letI := ((S.residueFieldCongr hs).inv ≫ f.residueFieldMap x.val).hom.toAlgebra
      PurelyTranscendental (S.residueField s) (X.residueField x.val)) :
    letI := ((V.toScheme.residueFieldCongr hs').inv ≫
      (f.resLE V U hUV).residueFieldMap x).hom.toAlgebra
    PurelyTranscendental (V.toScheme.residueField s') (U.toScheme.residueField x) := by
  subst s
  subst s'
  let _ : Algebra (S.residueField (f x.val)) (X.residueField (U.ι x)) :=
    (f.residueFieldMap x.val).hom.toAlgebra
  let := ((f.resLE V U hUV).residueFieldMap x).hom.toAlgebra
  have hH : PurelyTranscendental (S.residueField (f x.val)) (X.residueField (U.ι x)) := H
  show PurelyTranscendental (V.toScheme.residueField ((f.resLE V U hUV) x))
    (U.toScheme.residueField x)
  refine purelyTranscendental_of_ringEquiv
    ((S.residueFieldCongr (Scheme.Hom.coe_resLE_apply f hUV x)).symm ≪≫
      (asIso (V.ι.residueFieldMap ((f.resLE V U hUV) x)) :
        S.residueField (V.ι ((f.resLE V U hUV) x)) ≅
          V.toScheme.residueField ((f.resLE V U hUV) x))).commRingCatIsoToRingEquiv
    (asIso (U.ι.residueFieldMap x)).commRingCatIsoToRingEquiv ?_
  have hcomm := Scheme.Hom.residueFieldMap_congr (Scheme.Hom.resLE_comp_ι f hUV) x
  rw [Scheme.residueFieldMap_comp, Scheme.residueFieldMap_comp] at hcomm
  refine congrArg CommRingCat.Hom.hom ?_
  show ((S.residueFieldCongr (Scheme.Hom.coe_resLE_apply f hUV x)).inv ≫
      V.ι.residueFieldMap ((f.resLE V U hUV) x)) ≫ (f.resLE V U hUV).residueFieldMap x =
    f.residueFieldMap (U.ι x) ≫ U.ι.residueFieldMap x
  exact (Category.assoc _ _ _).trans
    ((Iso.inv_comp_eq (S.residueFieldCongr (Scheme.Hom.coe_resLE_apply f hUV x))).mpr hcomm)

end AlgebraicGeometry

end
