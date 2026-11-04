module

public import StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.CoherentKernels.FunctorRestriction
public import StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.CoherentKernels.KernelFinite
public import StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.CoherentKernels.QuasiFiniteSupport
public import
  StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.IntegralTransformQcoh.ExactKernelEquivalence
public import
  StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.IntegralTransformQcoh.KernelFullyFaithful

/-!
# Coherent kernels and exact functors of coherent modules

Let `k` be a field and let `X` and `Y` be schemes of finite type over `k` with `X` separated.
[Stacks, Tag 0FZN] says that sending a coherent `𝒪_{X ×_k Y}`-module `𝒦`, flat over `X` and with
support finite over `Y`, to the restriction to `Coh(𝒪_X)` of its integral transform
`𝓕 ↦ pr_{2,*}(pr_1^*𝓕 ⊗ 𝒦)` is an equivalence onto the `k`-linear exact functors
`Coh(𝒪_X) ⥤ Coh(𝒪_Y)`.

The proof follows the source. The integral transform of such a kernel is exact and `k`-linear
by [Stacks, Tag 0FZH], its higher direct images vanishing because the support is finite over
`Y`, and it preserves coherence by [Stacks, Tag 08DS]. Conversely a `k`-linear exact functor
`F` on coherent modules extends by [Stacks, Tag 0FZL] to a `k`-linear exact functor on
quasi-coherent modules commuting with direct sums, which by [Stacks, Tag 0FZH] is the integral
transform of a kernel `𝒦`; that kernel is coherent by [Stacks, Tag 0FZJ], and its support is
quasi-finite over `Y` by the count of the source, hence finite by [Stacks, Tag 0FZM]. Fullness
and faithfulness come from those of `𝒦 ↦ F_𝒦` and from the fact that a functor commuting with
filtered colimits is determined by its restriction to the coherent modules.

## Main definitions

* `AlgebraicGeometry.CoherentKernels.coherentIntegralTransformFunctor`: the functor of the tag.
* `AlgebraicGeometry.CoherentKernels.coherentIntegralTransformEquivalence`: the equivalence.

## Main results

* `AlgebraicGeometry.CoherentKernels.isEquivalence_coherentIntegralTransformFunctor`:
  **[Stacks, Tag 0FZN]**.

## References

* [Stacks Project, Tag 0FZN](https://stacks.math.columbia.edu/tag/0FZN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.SheafOfModules (CoherentModules)
open AlgebraicGeometry.CoherentModuleFunctors

universe u

namespace AlgebraicGeometry.CoherentKernels

variable (k : Type u) [Field k] (X Y : Over (Spec (.of k)))

/-- The source of a quasi-compact morphism to an affine scheme is compact. -/
private instance compactSpace_left_of_quasiCompact [QuasiCompact X.hom] :
    CompactSpace X.left :=
  QuasiCompact.compactSpace_of_compactSpace X.hom

/-- A scheme separated over a field is separated. -/
theorem isSeparated_terminal_from [IsSeparated X.hom] : IsSeparated (terminal.from X.left) := by
  rw [show terminal.from X.left = X.hom ≫ terminal.from _ from terminal.hom_ext _ _]
  infer_instance

/-- A scheme separated over a field has affine diagonal. -/
theorem isAffineHom_diagonal [IsSeparated X.hom] :
    IsAffineHom (pullback.diagonal (terminal.from X.left)) :=
  have := isSeparated_terminal_from k X
  inferInstance

/-- A scheme separated over a field is quasi-separated. -/
theorem quasiSeparatedSpace_left [IsSeparated X.hom] : QuasiSeparatedSpace X.left :=
  have := isAffineHom_diagonal k X
  inferInstance

/-- **The integral transform of a coherent kernel with support finite over `Y` preserves
coherence**, by [Stacks, Tag 08DS] in the form of
`isCoherent_integralTransformFormula_of_hasFiniteSupportOver`. -/
theorem preservesCoherent_quasicoherentIntegralTransform
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom]
    (K : (SheafOfModules.isQuasicoherent (pullback X.hom Y.hom).ringCatSheaf).FullSubcategory)
    (hK : finiteFlatCoherentKernel k X Y K) :
    letI : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
    letI := quasiSeparatedSpace_left k X
    PreservesCoherent (quasicoherentIntegralTransform k X Y K) := by
  let := quasiSeparatedSpace_left k X
  intro M
  obtain ⟨hc, -, hfin⟩ := hK
  have : K.obj.IsFiniteType := hc.isFiniteType
  have := isCoherent_integralTransformFormula_of_hasFiniteSupportOver k X Y K hfin
    ((coherentToQuasicoherent X.left).obj M) M.property
  exact @Stacks.AlgebraicGeometry.CoherentDevissage.isCoherent_of_iso _ _ _ _ _
    ((quasicoherentIntegralTransformData k X Y K).comparison.app _) this

/-! ### The functor from kernels to functors -/

section Functor

variable [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]

attribute [local instance] quasiSeparatedSpace_left

/-- Preserving coherence is invariant under isomorphism of functors. -/
theorem PreservesCoherent.of_iso {Z W : Scheme.{u}}
    {G G' : (SheafOfModules.isQuasicoherent Z.ringCatSheaf).FullSubcategory ⥤
      (SheafOfModules.isQuasicoherent W.ringCatSheaf).FullSubcategory}
    (e : G ≅ G') (hG : PreservesCoherent G) : PreservesCoherent G' := fun M =>
  ObjectProperty.prop_of_iso (P := fun N : SheafOfModules.{u} W.ringCatSheaf => N.IsCoherent)
    ((SheafOfModules.isQuasicoherent W.ringCatSheaf).ι.mapIso (e.app _)) (hG M)

/-- **A kernel of [Stacks, Tag 0FZH] whose integral transform preserves coherence lies in
category (2) of [Stacks, Tag 0FZN].** It is coherent by [Stacks, Tag 0FZJ], its support is
quasi-finite over `Y` by the fibre count of the source, hence finite by [Stacks, Tag 0FZM]. -/
theorem finiteFlatCoherentKernel_of_preservesCoherent
    (K : (SheafOfModules.isQuasicoherent (pullback X.hom Y.hom).ringCatSheaf).FullSubcategory)
    (hK : integralTransformExactKernel k X Y K)
    (hc : letI : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
      PreservesCoherent (quasicoherentIntegralTransform k X Y K)) :
    finiteFlatCoherentKernel k X Y K := by
  have : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  have hO : ((quasicoherentIntegralTransform k X Y K).obj
      (⟨SheafOfModules.unit X.left.ringCatSheaf,
        Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit X.left⟩ :
        (SheafOfModules.isQuasicoherent X.left.ringCatSheaf).FullSubcategory)).obj.IsCoherent :=
    hc ⟨SheafOfModules.unit X.left.ringCatSheaf,
      Stacks.AlgebraicGeometry.CoherentOfFiniteType.isCoherent_unit⟩
  have hcoh : K.obj.IsCoherent := isCoherent_of_integralTransformExactKernel k X Y K hK hO
  have := isAffineHom_diagonal k X
  have hcolim : PreservesFiniteColimits (quasicoherentIntegralTransform k X Y K) :=
    ((exactFunctor_iff _).mp
      (exactLinearCoproductFunctor_quasicoherentIntegralTransform k X Y K hK).2.1).2
  exact ⟨hcoh, hK.1, hasFiniteSupportOver_of_locallyQuasiFinite k X Y K hK
    (locallyQuasiFinite_schemeTheoreticSupport_of_exact k X Y K hcolim
      (fun M hM => hc ⟨M.obj, hM⟩)) hO⟩

/-- **The functor of [Stacks, Tag 0FZN]**: a coherent kernel on `X ×_k Y`, flat over `X` with
support finite over `Y`, is sent to the restriction of its integral transform
`𝓕 ↦ pr_{2,*}(pr_1^*𝓕 ⊗ 𝒦)` to the coherent modules. -/
def coherentIntegralTransformFunctor :
    (finiteFlatCoherentKernel k X Y).FullSubcategory ⥤
      (exactLinearCoherentFunctor k X Y).FullSubcategory :=
  letI : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  ObjectProperty.lift (exactLinearCoproductCoherentFunctor k X Y)
    ((finiteFlatCoherentKernel k X Y).ι ⋙ integralTransformQcohFunctor k X Y)
    (fun K => ⟨have := isAffineHom_diagonal k X
      exactLinearCoproductFunctor_quasicoherentIntegralTransform k X Y K.obj
        (integralTransformExactKernel_of_finiteFlatCoherentKernel k X Y K.obj K.property),
      preservesCoherent_quasicoherentIntegralTransform k X Y K.obj K.property⟩) ⋙
    coherentRestrictionFunctor k X Y

omit [QuasiCompact Y.hom] in
/-- The functor of [Stacks, Tag 0FZN] sends a kernel to the restriction of its integral
transform to the coherent modules. -/
theorem coherentIntegralTransformFunctor_obj_obj_comp
    (K : (finiteFlatCoherentKernel k X Y).FullSubcategory) :
    letI : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
    ((coherentIntegralTransformFunctor k X Y).obj K).obj ⋙ coherentToQuasicoherent Y.left =
      coherentToQuasicoherent X.left ⋙ quasicoherentIntegralTransform k X Y K.obj :=
  rfl

/-- The functor `coherentIntegralTransformFunctor` is faithful. -/
instance : (coherentIntegralTransformFunctor k X Y).Faithful := by
  let : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  have := isAffineHom_diagonal k X
  have := faithful_integralTransformQcohFunctor k X Y
  have := isNoetherian_of_finiteType_over_field k X
  have := (fullyFaithfulCoherentRestrictionFunctor k X Y).faithful
  unfold coherentIntegralTransformFunctor
  infer_instance

/-- The functor `coherentIntegralTransformFunctor` is full. -/
instance : (coherentIntegralTransformFunctor k X Y).Full := by
  let : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  have := isAffineHom_diagonal k X
  have := full_integralTransformQcohFunctor k X Y
  have := isNoetherian_of_finiteType_over_field k X
  have := (fullyFaithfulCoherentRestrictionFunctor k X Y).full
  unfold coherentIntegralTransformFunctor
  infer_instance

/-- The functor `coherentIntegralTransformFunctor` is essentially surjective: every `k`-linear
exact functor `Coh(𝒪_X) ⥤ Coh(𝒪_Y)` is isomorphic to the restriction of the integral transform
of a kernel. -/
instance : (coherentIntegralTransformFunctor k X Y).EssSurj := by
  let : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  have := isNoetherian_of_finiteType_over_field k X
  have := isNoetherian_of_finiteType_over_field k Y
  refine ⟨fun F => ?_⟩
  let G := extensionObj k X Y F
  have := isAffineHom_diagonal k X
  obtain ⟨K, hK, ⟨e⟩⟩ := exists_integralTransformExactKernel_iso k X Y G.obj G.property.1
  have hc : PreservesCoherent (quasicoherentIntegralTransform k X Y K) :=
    PreservesCoherent.of_iso e G.property.2
  exact ⟨⟨K, finiteFlatCoherentKernel_of_preservesCoherent k X Y K hK hc⟩,
    ⟨(coherentRestrictionFunctor k X Y).mapIso (ObjectProperty.isoMk _ e.symm) ≪≫
      ObjectProperty.isoMk _ (coherentRestrictionExtensionIso k X Y F)⟩⟩

/-- **Stacks Project, Tag 0FZN.** Let `k` be a field and let `X` and `Y` be schemes of finite
type over `k` with `X` separated. Sending a coherent `𝒪_{X ×_k Y}`-module `𝒦`, flat over `X` and
with support finite over `Y`, to the restriction to `Coh(𝒪_X)` of its integral transform
`𝓕 ↦ pr_{2,*}(pr_1^*𝓕 ⊗ 𝒦)` is an equivalence of categories onto the `k`-linear exact functors
`Coh(𝒪_X) ⥤ Coh(𝒪_Y)`.

Finite type over `k` is `LocallyOfFiniteType` together with `QuasiCompact`; `X ×_k Y` is the
fibre product over `Spec k`. The functor is `coherentIntegralTransformFunctor`, whose value at
`𝒦` is by definition the restriction of `quasicoherentIntegralTransform k X Y 𝒦`
(`coherentIntegralTransformFunctor_obj_obj_comp`), the pullback--tensor--pushforward formula
`integralTransformFormula` after forgetting quasi-coherence. -/
@[stacks 0FZN "sending a coherent kernel flat over X with support finite over Y to the \
restriction to Coh of its integral transform is an equivalence onto the k-linear exact functors \
Coh(O_X) to Coh(O_Y)"]
theorem isEquivalence_coherentIntegralTransformFunctor :
    (coherentIntegralTransformFunctor k X Y).IsEquivalence where

/-- The equivalence of [Stacks, Tag 0FZN], whose functor is
`coherentIntegralTransformFunctor`. -/
def coherentIntegralTransformEquivalence :
    (finiteFlatCoherentKernel k X Y).FullSubcategory ≌
      (exactLinearCoherentFunctor k X Y).FullSubcategory :=
  have := isEquivalence_coherentIntegralTransformFunctor k X Y
  (coherentIntegralTransformFunctor k X Y).asEquivalence

/-- **Every `k`-linear exact functor `Coh(𝒪_X) ⥤ Coh(𝒪_Y)` is the restriction of the integral
transform of a coherent kernel flat over `X` with support finite over `Y`.** -/
theorem exists_finiteFlatCoherentKernel_iso
    (F : (exactLinearCoherentFunctor k X Y).FullSubcategory) :
    letI : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
    ∃ K : (finiteFlatCoherentKernel k X Y).FullSubcategory,
      Nonempty (coherentToQuasicoherent X.left ⋙ quasicoherentIntegralTransform k X Y K.obj ≅
        F.obj ⋙ coherentToQuasicoherent Y.left) := by
  obtain ⟨K, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage (F := coherentIntegralTransformFunctor k X Y) F
  exact ⟨K, ⟨eqToIso (coherentIntegralTransformFunctor_obj_obj_comp k X Y K).symm ≪≫
    Functor.isoWhiskerRight ((ObjectProperty.ι _).mapIso e) (coherentToQuasicoherent Y.left)⟩⟩

end Functor

end AlgebraicGeometry.CoherentKernels

end
