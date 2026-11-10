module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Topology.GDelta.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FiniteTypeExtension
public import StacksFrontier.AlgebraicGeometry.Cohomology.LocallyNoetherian.SubQuotient
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.AffineComparison
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.EmbeddedCharacterization
public import StacksFrontier.AlgebraicGeometry.Divisors.EmbeddedPoints.NowhereDense
public import StacksFrontier.AlgebraicGeometry.Divisors.EmbeddedPoints.SupportStalk
public import StacksFrontier.AlgebraicGeometry.Divisors.EmbeddedPoints.SupportedSectionsQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Divisors.EmbeddedPoints.SupportedSectionsStalk
public import StacksFrontier.AlgebraicGeometry.AffineQcohPushforward.Colimits
public import StacksFrontier.AlgebraicGeometry.QcohLimits.Basic
public import StacksFrontier.RingTheory.Ideal.AssociatedPrime.Embedded

/-!
# Removing embedded points from a coherent sheaf

On a locally Noetherian scheme, call a subobject of a coherent module *nowhere dense coherent* if
it is coherent and its support is nowhere dense in the support of the ambient module. Such
subobjects have a greatest member, and the quotient by it has the same support as the module, has
no embedded associated points, and agrees with the module on a dense open.

The greatest member is produced in two steps. The supremum of all nowhere dense coherent
subobjects need not be coherent, so one passes to the largest quasi-coherent subobject contained
in it, which is coherent because a quasi-coherent submodule of a coherent module on a locally
Noetherian scheme is coherent. Its support is nowhere dense because, on an affine open, the
generic point of an irreducible component of the support avoids the support of every member of the
family, so the stalk of the supremum vanishes there.

The three properties of the quotient all rest on the description of the support as the set of
points with nontrivial stalk. Because the subobject has nowhere dense support, the points of the
support of the module that avoid the support of the subobject are dense in it; at such a point the
quotient map is an isomorphism on stalks, so the point lies in the support of the quotient, whose
support is closed and therefore contains the whole support of the module. Taking the open
complement of the support of the subobject gives an open on which the quotient map is a stalkwise
isomorphism, hence an isomorphism on sections. For the absence of embedded associated points one
argues by contradiction: an embedded associated point `x` of the quotient has nowhere dense
closure inside the support, so the sections of the quotient supported on that closure form a
quasi-coherent submodule whose preimage in the module is again nowhere dense coherent, hence
contained in the greatest one; that forces the submodule to vanish, contradicting the existence of
a section of the quotient whose colon ideal is the prime of `x`.

## Main definitions

* `Stacks.AlgebraicGeometry.EmbeddedPoints.IsNowhereDenseCoherentSubobject`: a coherent subobject
  whose support is nowhere dense in the support of the ambient module.

## Main results

* `Stacks.AlgebraicGeometry.EmbeddedPoints.exists_greatest_isNowhereDenseCoherentSubobject`: the
  nowhere dense coherent subobjects have a greatest member.
* `Stacks.AlgebraicGeometry.EmbeddedPoints.supp_cokernel_eq`: the quotient has the same support
  as the module.
* `Stacks.AlgebraicGeometry.EmbeddedPoints.cokernel_hasNoEmbeddedAssociatedPoints`: the quotient
  by the greatest such subobject has no embedded associated points.
* `Stacks.AlgebraicGeometry.EmbeddedPoints.exists_denseOpen_cokernel_iso`: there is a dense open,
  meeting the support densely, over every open subset of which the quotient map is an isomorphism
  on sections.

## Implementation notes

Subsheaves are subobjects in the category of sheaves of modules, and the quotient by a subobject
is the cokernel of its inclusion. Nowhere denseness is taken in the subspace topology on the
support of the ambient module. The last assertion is phrased as an isomorphism on sections over
every open contained in the chosen dense open; that is what pins down the identification of the
two restrictions.

Several instances are supplied positionally rather than by synthesis. The category structure on
`X.Modules` and the one on `SheafOfModules X.ringCatSheaf` are definitionally but not reducibly
equal, so a `Mono`, `Epi`, `HasColimit` or `PreservesColimit` instance stated in one spelling is
not found by instance search in the other; and for the same reason an equation such as
`Functor.map_comp` or `Category.assoc` can fail as a rewrite against a goal that prints
identically to its left-hand side. Where that happens the needed equation is stated as a `have`
in the spelling of the goal and discharged by the library lemma up to definitional equality.

## References

* [Stacks Project, Tag 02OL](https://stacks.math.columbia.edu/tag/02OL)
* [Stacks Project, Tag 01Y1](https://stacks.math.columbia.edu/tag/01Y1)
* [Stacks Project, Tag 01B7](https://stacks.math.columbia.edu/tag/01B7)
* [Stacks Project, Tag 02OK](https://stacks.math.columbia.edu/tag/02OK)
* [Stacks Project, Tag 056J](https://stacks.math.columbia.edu/tag/056J)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Scheme.Modules

universe u

namespace Stacks.AlgebraicGeometry.EmbeddedPoints

variable {X : Scheme.{u}}

/-- A coherent subobject whose support is nowhere dense in the support of `F`. -/
def IsNowhereDenseCoherentSubobject (F : X.Modules) (K : Subobject F) : Prop :=
  (K : X.Modules).IsCoherent ∧
    IsNowhereDense
      {x : ↥((⟨F.val, F.isSheaf⟩ : RingedSpace.ModuleSheaf.{u} X.toRingedSpace).supp) |
        (x : X) ∈
      (⟨(K : X.Modules).val, (K : X.Modules).isSheaf⟩ :
            RingedSpace.ModuleSheaf.{u} X.toRingedSpace).supp}

/-- The quotient of a sheaf of modules of finite type by a subobject is of finite type, being a
quotient of it. -/
lemma isFiniteType_cokernel_arrow {F : X.Modules} (hF : F.IsFiniteType) (K : Subobject F) :
    (cokernel K.arrow).IsFiniteType :=
  @Stacks.SheafOfModules.isFiniteType_of_epi _ _ _ _ _ _ _ F (cokernel K.arrow)
    (cokernel.π K.arrow) coequalizer.π_epi hF

/-- A subobject whose stalk map at `x` vanishes is not supported at `x`. -/
private theorem notMem_supp_of_stalkFunctor_map_eq_zero {M N : X.Modules} (f : M ⟶ N) (hf : Mono f)
    (x : X) (h : (AlgebraicGeometry.SheafOfModules.stalkFunctor X.ringCatSheaf x).map f = 0) :
    x ∉ (⟨M.val, M.isSheaf⟩ : RingedSpace.ModuleSheaf X.toRingedSpace).supp := by
  rw [supp_eq_setOf_nontrivial_stalk]
  have hinj := injective_stalkFunctor_map f hf x
  exact fun hnon ↦ (not_nontrivial_iff_subsingleton.mpr ⟨fun a b ↦ hinj (by rw [h]; simp)⟩) hnon

/-- The points of the support of `F` outside the support of a nowhere dense coherent subobject
are dense in the support of `F`. -/
private theorem dense_setOf_notMem_supp_of_isNowhereDenseCoherentSubobject {F : X.Modules}
    {K : Subobject F} (hK : IsNowhereDenseCoherentSubobject F K) :
    Dense {x : ↥((⟨F.val, F.isSheaf⟩ : RingedSpace.ModuleSheaf.{u} X.toRingedSpace).supp) |
      (x : X) ∉ (⟨(K : X.Modules).val, (K : X.Modules).isSheaf⟩ :
        RingedSpace.ModuleSheaf.{u} X.toRingedSpace).supp} :=
  (isClosed_isNowhereDense_iff_compl.mp
    ⟨(isClosed_supp_of_isFiniteType _ hK.1.isFiniteType).preimage continuous_subtype_val,
      hK.2⟩).2

/-- **Stacks Project, Tag 02OL, maximal subsheaf.** The coherent subsheaves whose support is
nowhere dense in the support of `F` have a greatest member. -/
@[stacks 02OL "greatest subsheaf"]
theorem exists_greatest_isNowhereDenseCoherentSubobject [IsLocallyNoetherian X]
    (F : X.Modules) [F.IsCoherent] :
    ∃ K : Subobject F,
      IsNowhereDenseCoherentSubobject F K ∧
        ∀ L : Subobject F, IsNowhereDenseCoherentSubobject F L → L ≤ K := by
  classical
  let SF : Set X := (⟨F.val, F.isSheaf⟩ : RingedSpace.ModuleSheaf X.toRingedSpace).supp
  let S : Set (Subobject F) := {L | IsNowhereDenseCoherentSubobject F L}
  have hSFclosed : IsClosed SF := isClosed_supp_of_isFiniteType F ‹F.IsCoherent›.isFiniteType
  have hFqc : F.IsQuasicoherent := isQuasicoherent_of_isCoherent F
  obtain ⟨K, hKG, hKqc, hKmax⟩ :=
    exists_largest_quasicoherent_subobject F hFqc (sSup S : Subobject F)
  have hKcoh : (K : X.Modules).IsCoherent :=
    @Stacks.AlgebraicGeometry.CoherentTFAE.isCoherent_of_mono_of_isQuasicoherent X _ F
      (K : X.Modules) ‹F.IsCoherent› hKqc K.arrow inferInstance
  have hKnd : IsNowhereDense
      {x : ↥SF | (x : X) ∈
        (⟨(K : X.Modules).val, (K : X.Modules).isSheaf⟩ :
          RingedSpace.ModuleSheaf X.toRingedSpace).supp} := by
    let SK : Set X := (⟨(K : X.Modules).val, (K : X.Modules).isSheaf⟩ :
      RingedSpace.ModuleSheaf X.toRingedSpace).supp
    have hKclosed : IsClosed SK :=
      isClosed_supp_of_isFiniteType (K : X.Modules) hKcoh.isFiniteType
    have hRelClosed : IsClosed {x : ↥SF | (x : X) ∈ SK} :=
      hKclosed.preimage continuous_subtype_val
    refine hRelClosed.isNowhereDense_iff.mpr (Set.eq_empty_iff_forall_notMem.mpr fun x hx ↦ ?_)
    obtain ⟨W, hWsub, hWopen, hxW⟩ := mem_interior.mp hx
    obtain ⟨U, hU, hxU, -⟩ :=
      exists_isAffineOpen_mem_and_subset (U := (⊤ : X.Opens)) (x := (x : X)) (by simp)
    let V : Set U := {z | z.1 ∈ SF}
    have hVclosed : IsClosed V := by
      change IsClosed (Subtype.val ⁻¹' SF)
      exact hSFclosed.preimage continuous_subtype_val
    have : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
    have : NoetherianSpace U := noetherianSpace_of_isAffineOpen U hU
    have : NoetherianSpace (Set.univ : Set U) :=
      (noetherianSpace_set_iff _).2 (fun t _ ↦ NoetherianSpace.isCompact (t : Set U))
    have : NoetherianSpace V := NoetherianSpace.of_subset (W := Set.univ) (V := V) (by simp)
    have : QuasiSober V := hVclosed.isClosedEmbedding_subtypeVal.quasiSober
    let z : V := ⟨⟨(x : X), hxU⟩, x.2⟩
    let Z : Set V := irreducibleComponent z
    have hZ : Z ∈ irreducibleComponents V := irreducibleComponent_mem_irreducibleComponents z
    let y : V := hZ.1.genericPoint
    have hy : IsGenericPoint y Z := hZ.1.isGenericPoint_genericPoint
      (isClosed_of_mem_irreducibleComponents Z hZ)
    let e₀ : V ≃ₜ {q : ↥SF // (q : X) ∈ U} := subtypeCommHomeomorph (U : Set X) SF
    let e : V → ↥SF := fun q ↦ (e₀ q).1
    have he : Topology.IsOpenEmbedding e := by
      have hUrel : IsOpen {q : ↥SF | (q : X) ∈ U} := U.2.preimage continuous_subtype_val
      change Topology.IsOpenEmbedding
        ((Subtype.val : {q : ↥SF // (q : X) ∈ U} → ↥SF) ∘ e₀)
      exact hUrel.isOpenEmbedding_subtypeVal.comp e₀.isOpenEmbedding
    have hyW : y ∈ e ⁻¹' W := by
      refine (hy.mem_open_set_iff (hWopen.preimage he.continuous)).2
        ⟨z, mem_irreducibleComponent, ?_⟩
      change e z ∈ W
      have hez : e z = x := Subtype.ext rfl
      rwa [hez]
    have hyK : (e y : X) ∈ SK := hWsub hyW
    have hGzero : IsZero ((AlgebraicGeometry.SheafOfModules.stalkFunctor
        X.ringCatSheaf (e y : X)).obj ((sSup S : Subobject F) : X.Modules)) := by
      refine isZero_stalkFunctor_obj_sSup F S (e y : X) fun L hL ↦ ?_
      exact isZero_stalkFunctor_obj_of_notMem_supp (L : X.Modules)
        (notMem_of_isGenericPoint_of_isNowhereDense e he
          ((isClosed_supp_of_isFiniteType (L : X.Modules) hL.1.isFiniteType).preimage
            continuous_subtype_val) hL.2 hZ hy)
    set T := AlgebraicGeometry.SheafOfModules.stalkFunctor X.ringCatSheaf (e y : X) with hT
    have hmapzero : T.map K.arrow = 0 := by
      rw [← Subobject.ofLE_arrow hKG]
      exact (T.map_comp _ _).trans (by
        rw [hGzero.eq_of_src (T.map (sSup S : Subobject F).arrow) 0]
        exact comp_zero)
    exact notMem_supp_of_stalkFunctor_map_eq_zero K.arrow inferInstance _ hmapzero hyK
  exact ⟨K, ⟨hKcoh, hKnd⟩, fun L hL ↦ hKmax L (Subobject.le_sSup S L hL)
    (@isQuasicoherent_of_isCoherent _ _ _ (L : X.Modules) hL.1)⟩

/-- **Stacks Project, Tag 02OL, part (1).** The quotient has the same support. -/
@[stacks 02OL "part (1): support of the quotient"]
theorem supp_cokernel_eq [IsLocallyNoetherian X] (F : X.Modules) [F.IsCoherent] (K : Subobject F)
    (hK : IsNowhereDenseCoherentSubobject F K) :
    (⟨(cokernel K.arrow).val, (cokernel K.arrow).isSheaf⟩ :
      RingedSpace.ModuleSheaf.{u} X.toRingedSpace).supp =
      (⟨F.val, F.isSheaf⟩ : RingedSpace.ModuleSheaf.{u} X.toRingedSpace).supp := by
  classical
  let SF : Set X := (⟨F.val, F.isSheaf⟩ : RingedSpace.ModuleSheaf X.toRingedSpace).supp
  let SK : Set X := (⟨(K : X.Modules).val, (K : X.Modules).isSheaf⟩ :
    RingedSpace.ModuleSheaf X.toRingedSpace).supp
  let SQ : Set X := (⟨(cokernel K.arrow).val, (cokernel K.arrow).isSheaf⟩ :
    RingedSpace.ModuleSheaf X.toRingedSpace).supp
  have hQclosed : IsClosed SQ :=
    isClosed_supp_of_isFiniteType _
      (isFiniteType_cokernel_arrow ‹F.IsCoherent›.isFiniteType K)
  have hSdense : Dense {x : ↥SF | (x : X) ∉ SK} :=
    dense_setOf_notMem_supp_of_isNowhereDenseCoherentSubobject hK
  have himage : Subtype.val '' {x : ↥SF | (x : X) ∉ SK} ⊆ SQ := by
    rintro x ⟨y, hy, rfl⟩
    exact mem_supp_cokernel_of_mem_supp_of_notMem_supp F K y.2 hy
  have hclosure : closure (Subtype.val '' {x : ↥SF | (x : X) ∉ SK}) ⊆ SQ :=
    closure_minimal himage hQclosed
  have hdenseImage : SF ⊆ closure (Subtype.val '' {x : ↥SF | (x : X) ∉ SK}) :=
    (Subtype.dense_iff (s := SF) (t := {x : ↥SF | (x : X) ∉ SK})).mp hSdense
  exact Set.Subset.antisymm (supp_cokernel_subset_supp F K)
    fun x hx ↦ hclosure (hdenseImage hx)

/-- **Stacks Project, Tag 02OL, part (2).** The quotient by a greatest nowhere dense coherent
subobject has no embedded associated points. -/
@[stacks 02OL "part (2): no embedded associated points"]
theorem cokernel_hasNoEmbeddedAssociatedPoints [IsLocallyNoetherian X]
    (F : X.Modules) [F.IsCoherent] (K : Subobject F)
    (hK : IsNowhereDenseCoherentSubobject F K)
    (hmax : ∀ L : Subobject F, IsNowhereDenseCoherentSubobject F L → L ≤ K) :
    HasNoEmbeddedAssociatedPoints (cokernel K.arrow) := by
  classical
  let Q := cokernel K.arrow
  have hKqc : (K : X.Modules).IsQuasicoherent :=
    @isQuasicoherent_of_isCoherent _ _ _ (K : X.Modules) hK.1
  have hFqc : F.IsQuasicoherent := isQuasicoherent_of_isCoherent F
  have hQqc : Q.IsQuasicoherent :=
    @Stacks.AlgebraicGeometry.QuasicoherentColimits.isQuasicoherent_cokernel _ _ _ K.arrow
      hKqc hFqc
  have hQcoh : Q.IsCoherent :=
    @Stacks.AlgebraicGeometry.CoherentTFAE.isCoherent_of_epi_of_isQuasicoherent X _ F Q
      ‹F.IsCoherent› hQqc (cokernel.π K.arrow) coequalizer.π_epi
  intro x hx
  have hxng := (@AlgebraicGeometry.isEmbeddedAssociatedPoint_iff_not_genericPoint X _ Q hQcoh
    x).mp hx
  let SF := (⟨F.val, F.isSheaf⟩ : RingedSpace.ModuleSheaf X.toRingedSpace).supp
  let SK := (⟨(K : X.Modules).val, (K : X.Modules).isSheaf⟩ :
    RingedSpace.ModuleSheaf X.toRingedSpace).supp
  have hQS : SheafOfModules.supp Q = SF := by
    rw [← SheafOfModules.supp_eq_moduleSheaf_supp (F := Q)]
    exact supp_cokernel_eq F K hK
  have hxSF : x ∈ SF := by
    rw [← hQS]
    exact AlgebraicGeometry.associatedPoints_subset_support Q hxng.1
  have hng : ¬ ∃ Z ∈ irreducibleComponents (↥SF), IsGenericPoint x (Subtype.val '' Z) := by
    rw [← hQS]
    exact hxng.2
  let Z : Set X := closure ({x} : Set X)
  have hZnd : IsNowhereDense {y : ↥SF | (y : X) ∈ Z} :=
    isNowhereDense_setOf_mem_closure_singleton SF
      (isClosed_supp_of_isFiniteType F ‹F.IsCoherent›.isFiniteType) hxSF hng
  let H := Scheme.Modules.supportedSectionsSubmodule Z Q
  let HM : X.Modules := H.toSheafOfModules
  let hι : HM ⟶ Q := H.ι
  have hHqc : H.toSheafOfModules.IsQuasicoherent :=
    supportedSectionsSubmodule_isQuasicoherent Z isClosed_closure
      (isRetrocompact_of_isLocallyNoetherian _) Q hQqc
  have hHmono : Mono hι := SheafOfModules.Submodule.instMonoι H
  have hcokHqc : (cokernel hι).IsQuasicoherent :=
    @Stacks.AlgebraicGeometry.QuasicoherentColimits.isQuasicoherent_cokernel _ _ _ hι
      hHqc hQqc
  let f : F ⟶ cokernel hι := cokernel.π K.arrow ≫ cokernel.π hι
  have hkerqc : (kernel f).IsQuasicoherent :=
    @Stacks.AlgebraicGeometry.QcohLimits.isQuasicoherent_kernel _ _ _ f hFqc hcokHqc
  let L : Subobject F := Subobject.mk (kernel.ι f)
  have hLqc : (L : X.Modules).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
      (Subobject.underlyingIso (kernel.ι f)).symm hkerqc
  have hLcoh : (L : X.Modules).IsCoherent :=
    @Stacks.AlgebraicGeometry.CoherentTFAE.isCoherent_of_mono_of_isQuasicoherent X _ F
      (L : X.Modules) ‹F.IsCoherent› hLqc L.arrow inferInstance
  have hLcond : L.arrow ≫ f = 0 := by
    dsimp only [L]
    rw [← Subobject.underlyingIso_hom_comp_eq_mk]
    simp
  have hLnd : IsNowhereDense {y : ↥SF | (y : X) ∈
      (⟨(L : X.Modules).val, (L : X.Modules).isSheaf⟩ :
        RingedSpace.ModuleSheaf X.toRingedSpace).supp} := by
    refine (hK.2.union hZnd).mono fun y hy ↦ ?_
    by_contra hn
    have hnK : (y : X) ∉ SK := fun h ↦ hn (Or.inl h)
    have hnZ : (y : X) ∉ Z := fun h ↦ hn (Or.inr h)
    set T := AlgebraicGeometry.SheafOfModules.stalkFunctor X.ringCatSheaf (y : X) with hT
    have hKzero : IsZero (T.obj (K : X.Modules)) :=
      isZero_stalkFunctor_obj_of_notMem_supp _ hnK
    have hHzero : IsZero (T.obj HM) :=
      isZero_stalkFunctor_obj_supportedSections Z Q hnZ
    have hπK : IsIso (T.map (cokernel.π K.arrow)) :=
      isIso_map_cokernelπ_of_isZero T K.arrow hKzero
    have hπH : IsIso (T.map (cokernel.π hι)) :=
      isIso_map_cokernelπ_of_isZero T hι hHzero
    have hmc : T.map f = T.map (cokernel.π K.arrow) ≫ T.map (cokernel.π hι) := T.map_comp _ _
    have hfi : IsIso (T.map f) := by
      rw [hmc]
      exact @IsIso.comp_isIso _ _ _ _ _ _ _ hπK hπH
    have hmc2 : T.map L.arrow ≫ T.map f = T.map (L.arrow ≫ f) := (T.map_comp _ _).symm
    have hmz : T.map (L.arrow ≫ f) = 0 :=
      (congrArg (fun g : (L : X.Modules) ⟶ cokernel hι ↦ T.map g) hLcond).trans
        (Functor.map_zero T _ _)
    have hz : T.map L.arrow = 0 := by
      refine (@cancel_mono _ _ _ _ _ (T.map f) (@IsIso.mono_of_iso _ _ _ _ _ hfi) _ _).mp ?_
      rw [hmc2, hmz, zero_comp]
    exact notMem_supp_of_stalkFunctor_map_eq_zero L.arrow inferInstance _ hz hy
  have hLK := hmax L ⟨hLcoh, hLnd⟩
  have hLπ : L.arrow ≫ cokernel.π K.arrow = 0 := by
    rw [← Subobject.ofLE_arrow hLK, Category.assoc, cokernel.condition, comp_zero]
  have hkπ : kernel.ι f ≫ cokernel.π K.arrow = 0 := by
    rw [← Subobject.underlyingIso_arrow (kernel.ι f), Category.assoc, hLπ, comp_zero]
  have haf : pullback.fst (cokernel.π K.arrow) hι ≫ f = 0 := by
    dsimp only [f]
    rw [← Category.assoc, pullback.condition, Category.assoc, cokernel.condition, comp_zero]
  have haπ : pullback.fst (cokernel.π K.arrow) hι ≫ cokernel.π K.arrow = 0 := by
    rw [← kernel.lift_ι f (pullback.fst (cokernel.π K.arrow) hι) haf, Category.assoc, hkπ,
      comp_zero]
  have hHz : hι = 0 := by
    refine (cancel_epi (pullback.snd (cokernel.π K.arrow) hι)).mp ?_
    rw [comp_zero]
    exact pullback.condition.symm.trans haπ
  obtain ⟨U, hU, hxU, -⟩ :=
    exists_isAffineOpen_mem_and_subset (U := (⊤ : X.Opens)) (x := x) (by simp)
  obtain ⟨hp, s, hs⟩ :=
    (@AlgebraicGeometry.isAssociatedPrime_sections_iff_isAssociatedPoint_of_isLocallyNoetherian
      X _ Q hQqc U hU x hxU).mpr hx.1
  have hsH : s ∈ H.toSubmodule.obj (op U) :=
    mem_supportedSectionsSubmodule_closure_singleton Q U hU hxU s hs
  have hs0 : s = 0 :=
    congrArg (fun g : HM ⟶ Q ↦
      g.val.app (op U) (⟨s, hsH⟩ : HM.val.obj (op U))) hHz
  rw [hs0, Submodule.span_zero_singleton, Submodule.colon_bot] at hs
  exact hp.ne_top hs.symm

/-- **Stacks Project, Tag 02OL, part (3).** The canonical quotient map becomes an isomorphism on
a dense open meeting the support densely. -/
@[stacks 02OL "part (3): agreement on a dense open"]
theorem exists_denseOpen_cokernel_iso [IsLocallyNoetherian X] (F : X.Modules) [F.IsCoherent]
    (K : Subobject F) (hK : IsNowhereDenseCoherentSubobject F K) :
    ∃ U : X.Opens,
      Dense (U : Set X) ∧
      Dense {x : ↥((⟨F.val, F.isSheaf⟩ :
            RingedSpace.ModuleSheaf.{u} X.toRingedSpace).supp) | (x : X) ∈ U} ∧
          ∀ V : X.Opens, V ≤ U →
            IsIso ((cokernel.π K.arrow).val.app (op V)) := by
  classical
  let SF : Set X := (⟨F.val, F.isSheaf⟩ : RingedSpace.ModuleSheaf X.toRingedSpace).supp
  let SK : Set X := (⟨(K : X.Modules).val, (K : X.Modules).isSheaf⟩ :
    RingedSpace.ModuleSheaf X.toRingedSpace).supp
  have hKsub : SK ⊆ SF := supp_subobject_subset_supp F K
  have hSKclosed : IsClosed SK :=
    isClosed_supp_of_isFiniteType _ hK.1.isFiniteType
  have hRelDense : Dense {x : ↥SF | (x : X) ∉ SK} :=
    dense_setOf_notMem_supp_of_isNowhereDenseCoherentSubobject hK
  let U : X.Opens := ⟨SKᶜ, hSKclosed.isOpen_compl⟩
  let j : ↥SF → X := fun x ↦ x.1
  have hj : Continuous j := continuous_subtype_val
  have hUdense : Dense (U : Set X) := by
    rw [dense_iff_inter_open]
    intro W hW hWne
    by_cases hWF : (W ∩ SF).Nonempty
    · have hne : (j ⁻¹' W).Nonempty := by
        obtain ⟨x, hxW, hxF⟩ := hWF
        exact ⟨⟨x, hxF⟩, hxW⟩
      obtain ⟨x, hxW, hxnotK⟩ :=
        hRelDense.inter_open_nonempty (j ⁻¹' W) (hW.preimage hj) hne
      exact ⟨x.1, hxW, hxnotK⟩
    · obtain ⟨x, hxW⟩ := hWne
      exact ⟨x, hxW, fun hxK ↦ hWF ⟨x, hxW, hKsub hxK⟩⟩
  refine ⟨U, hUdense, by simpa [U, SF, SK] using hRelDense, ?_⟩
  intro V hVU
  let T := AlgebraicGeometry.SheafOfModules.stalkFunctor X.ringCatSheaf
  let f := (SheafOfModules.toSheaf X.ringCatSheaf).map (cokernel.π K.arrow)
  have hst : ∀ x : V, IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x.1).map f.hom) := by
    intro x
    have hπ : IsIso ((T x.1).map (cokernel.π K.arrow)) :=
      isIso_map_cokernelπ_of_isZero (T x.1) K.arrow
        (isZero_stalkFunctor_obj_of_notMem_supp _ (hVU x.2))
    exact ((forget₂ (ModuleCat _) AddCommGrpCat).mapIso
      (@asIso _ _ _ _ ((T x.1).map (cokernel.π K.arrow)) hπ)).isIso_hom
  have hadd : IsIso (f.hom.app (op V)) :=
    @TopCat.Presheaf.app_isIso_of_stalkFunctor_map_iso AddCommGrpCat.{u} _ _ _ _ _ _ _ _ _ _ _ _ _
      f V hst
  have hcomponents :
      (forget₂ (ModuleCat (X.ringCatSheaf.obj.obj (op V))) AddCommGrpCat).map
          ((cokernel.π K.arrow).val.app (op V)) = f.hom.app (op V) := rfl
  have hiso : IsIso ((forget₂ (ModuleCat (X.ringCatSheaf.obj.obj (op V)))
    AddCommGrpCat).map ((cokernel.π K.arrow).val.app (op V))) := hcomponents ▸ hadd
  exact @isIso_of_reflects_iso _ _ _ _ _ _ ((cokernel.π K.arrow).val.app (op V))
    (forget₂ (ModuleCat (X.ringCatSheaf.obj.obj (op V))) AddCommGrpCat) hiso _

end Stacks.AlgebraicGeometry.EmbeddedPoints

end
