module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorFiniteness
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.CapTensorPullback
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.ModuleBaseChange
public import StacksFrontier.AlgebraicGeometry.Morphisms.FlatMorphisms.BaseChange
public import StacksFrontier.AlgebraicGeometry.PullbackTensor.StalkFormula
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.Trdeg
public import StacksFrontier.CategoryTheory.Sites.Modules.TensorProduct.Basic
public import StacksFrontier.Topology.Sheaves.Cohomology.MayerVietorisAndLimits.InverseSystemsOnASpace
public import StacksCore.Tactic.StacksAttribute

/-!
# Composing the families of cycles attached to two modules

Let `X --f--> Y --g--> S` be morphisms of schemes, both locally of finite type, let `F` be a
quasi-coherent `𝒪_X`-module of finite type whose support on every fibre of `f` has dimension at
most `r`, and let `G` be a quasi-coherent `𝒪_Y`-module of finite type whose support on every
fibre of `g` has dimension at most `e`. This file proves that when `F` is flat over `Y` the
composition `[F/X/Y]_r ∘ [G/Y/S]_e` of the two associated families is the family
`[F ⊗_{𝒪_X} f^* G/X/S]_{r + e}`.

The composition is defined on the fibre over a point `s` of `S` as the action, over the base
`Spec κ(s)`, of the base change of `[F/X/Y]_r` on the cycle `[G_s]_e`, read on `X ×_Y Y_s` and
transported to `X_s` along the canonical isomorphism `X ×_Y Y_s ≅ X_s`. So the proof is the
identification of all three factors on `X ×_Y Y_s`: the base change of the family is the family
of the base-changed module (Stacks 0H4R); the base-changed module is flat over `Y_s`; and the
action of the family of a flat module on the cycle of a module is the cycle of the tensor
product (Stacks 0H69). What that produces is the cycle of `F_s ⊗ f_s^* G_s` on `X ×_Y Y_s`, and
reading it back on `X_s` is the transport of an associated cycle along an isomorphism of the
scheme it lives on.

The dimension bound making the right-hand side well defined is obtained the same way, and it
needs the converse of the conversion performed by
`Stacks.Chow.fiberModule_schemeDeltaDimension_le`: over the spectrum of a field a bound on the
delta-dimension of the support of a coherent module is a bound on the topological dimension of
that support. The spectrum of a field is a Jacobson space on which the Chow dimension function
vanishes, so for an integral closed subscheme the delta-dimension at the generic point *is* the
topological dimension, and a scheme locally of finite type over such a base has dimension the
supremum over its irreducible components.

## Main definitions

* `Stacks.Chow.fibreTensorPullbackIso` — Stacks 01CD on the fibre: the restriction of
  `F ⊗_{𝒪_X} f^* G` to `X_s`, read on `X ×_Y Y_s`, is `F_s ⊗ f_s^* G_s`.

## Main results

* `Stacks.Chow.fiberModule_flatOver` — the pullback of a module flat over `Y` to `X ×_Y Y_s` is
  flat over `Y_s`.
* `Stacks.Chow.topologicalKrullDim_le_of_schemeDeltaDimension_le` — over a Jacobson base whose
  dimension function vanishes at closed points, a bound on the delta-dimension of a scheme
  locally of finite type is a bound on its topological dimension.
* `Stacks.Chow.topologicalKrullDim_supp_le_of_field_schemeDeltaDimension_le` — over the spectrum
  of a field, a bound on the delta-dimension of the support of a coherent module is a bound on
  the topological dimension of that support.
* `Stacks.Chow.topologicalKrullDim_supp_eq_of_isoPullback` — the dimension of the support is
  unchanged by pullback along an isomorphism of schemes.
* `Stacks.Chow.cycleAssociatedToCoherentSheaf_eq_of_source_iso` — the cycle associated to a
  coherent module read through an isomorphism of the scheme it lives on.
* `Stacks.Chow.tensorPullback_isFiniteType` and
  `Stacks.Chow.tensorPullback_isQuasicoherent` — `F ⊗_{𝒪_X} f^* G` is again quasi-coherent of
  finite type, the first observation of the source's proof.
* `Stacks.Chow.fibreDim_tensorPullback_le` — the support of `F ⊗_{𝒪_X} f^* G` on the fibre of
  `X/S` over `s` has dimension at most `r + e`, so the right-hand side is defined.
* `Stacks.Chow.compFamily_familyAssociatedToModule` — Stacks 0H6L, the equality of families.

## Implementation notes

The bound on the topological dimension is deduced from the delta-dimension bound component by
component. On an irreducible component `W` the delta-dimension is the relative dimension at the
generic point of `W`, which by Stacks 02QO is the topological dimension of the reduced closed
subscheme carried by `W`; that subscheme is homeomorphic to `W`. The reduction of the dimension
of the whole space to its components is the inequality half of the general topological statement,
proved here from `Order.krullDim_eq_iSup_height` and the fact that an irreducible closed subset
of a space has height at most the dimension of that subset as a subspace.

Both statements about an isomorphism `e : A ≅ B` of schemes use only that `e.hom` is an open
immersion, so neither multiplicity nor relative dimension has to be recomputed: they are
`Stacks.Chow.sheafMultiplicity_pullback_of_isOpenImmersion` and
`Stacks.Chow.relativeDimension_eq_of_openImmersion`.

Stacks 01CD on the fibre needs no new comparison of tensor products: the tensor product used by
`AlgebraicGeometry.tensorPullback` is
`Stacks.SheafOfModules.TensorStalkRingedSpace.tensorSheaf`, which is
`Stacks.RingedSpace.tensorSheaf` on the nose, and `AlgebraicGeometry.Scheme.Modules.pullback` is
`Stacks.RingedSpace.pullbackFunctor` on the underlying ringed spaces; so
`Stacks.RingedSpace.pullbackTensorIsoApp` applies directly, and the only other ingredient is
that the two ways of pulling `G` back to `X ×_Y Y_s` agree.

Finite type of the tensor product is Stacks 03L6 on the site of opens of the scheme; it is
stated there for a ringed site, and the ring sheaf of the ringed site attached to a ringed space
is the ring sheaf of that space, so the two hypotheses have to be re-typed over the former
before the statement applies.

## References

* [Stacks Project, Tag 01B6](https://stacks.math.columbia.edu/tag/01B6)
* [Stacks Project, Tag 01BG](https://stacks.math.columbia.edu/tag/01BG)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 01CE](https://stacks.math.columbia.edu/tag/01CE)
* [Stacks Project, Tag 01U8](https://stacks.math.columbia.edu/tag/01U8)
* [Stacks Project, Tag 02QO](https://stacks.math.columbia.edu/tag/02QO)
* [Stacks Project, Tag 02QX](https://stacks.math.columbia.edu/tag/02QX)
* [Stacks Project, Tag 03L6](https://stacks.math.columbia.edu/tag/03L6)
* [Stacks Project, Tag 0H4R](https://stacks.math.columbia.edu/tag/0H4R)
* [Stacks Project, Tag 0H69](https://stacks.math.columbia.edu/tag/0H69)
* [Stacks Project, Tag 0H6L](https://stacks.math.columbia.edu/tag/0H6L)
-/

@[expose] public noncomputable section

attribute [local implicit_reducible] Stacks.SheafOfModules.Tensor.ringSheaf

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### Flatness of the module on a fibre of the second morphism -/

/-- The pullback of a quasi-coherent `𝒪_X`-module flat over `Y` to the base change
`X ×_Y Y_s` of `f : X ⟶ Y` along the inclusion of the fibre of `g : Y ⟶ S` over `s` is flat
over `Y_s`: flatness over the base is preserved by base change (Stacks 01U8). -/
theorem fiberModule_flatOver {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S) (F : X.Modules)
    [F.IsQuasicoherent] (hflat : IsFlatOver f.toLRSHom.toShHom F) (s : S) :
    IsFlatOver (pullback.snd f (g.fiberι s)).toLRSHom.toShHom
      ((Scheme.Modules.pullback (pullback.fst f (g.fiberι s))).obj F) :=
  @modulePullback_isFlatOver X Y (g.fiber s) (pullback f (g.fiberι s)) f (g.fiberι s)
    (pullback.fst f (g.fiberι s)) (pullback.snd f (g.fiberι s))
    (IsPullback.of_hasPullback f (g.fiberι s)) F ‹F.IsQuasicoherent› hflat

/-! ### The topological dimension from the delta-dimension -/

/-- The preimage of an irreducible subset under the inclusion of a larger subset is
irreducible. -/
private theorem isIrreducible_preimage_val {T : Type*} [TopologicalSpace T] {a b : Set T}
    (ha : IsIrreducible a) (h : a ⊆ b) :
    IsIrreducible ((Subtype.val : b → T) ⁻¹' a) := by
  have := Subtype.irreducibleSpace ha
  have he : Set.inclusion h '' (Set.univ : Set a) = (Subtype.val : b → T) ⁻¹' a := by
    ext x; aesop
  rw [← he]
  exact (IrreducibleSpace.isIrreducible_univ a).image _ (by fun_prop)

/-- The dimension of a topological space is at most a bound satisfied by all of its irreducible
components: every irreducible closed subset is contained in a component, and its height is at
most the dimension of that component. -/
private theorem topologicalKrullDim_le_of_forall_irreducibleComponents {T : Type*}
    [TopologicalSpace T] {n : WithBot ℕ∞}
    (h : ∀ W ∈ irreducibleComponents T, topologicalKrullDim W ≤ n) :
    topologicalKrullDim T ≤ n := by
  rw [topologicalKrullDim, Order.krullDim_eq_iSup_height]
  refine iSup_le fun Z ↦ ?_
  obtain ⟨W, hW, hZW⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible
    (Z : Set T) Z.isIrreducible
  let W' : IrreducibleCloseds T := ⟨W, hW.1, isClosed_of_mem_irreducibleComponents W hW⟩
  calc (Order.height Z : WithBot ℕ∞) ≤ (Order.height W' : WithBot ℕ∞) :=
        WithBot.coe_le_coe.mpr (Order.height_mono (show Z ≤ W' from hZW))
    _ ≤ topologicalKrullDim W := AlgebraicGeometry.height_le_topologicalKrullDim W'
    _ ≤ n := h W hW

/-- **Stacks 02QO**, read as a bound on the topological dimension. Over a Jacobson base whose
dimension function vanishes at closed points, a scheme locally of finite type whose
delta-dimension is at most `n` has topological dimension at most `n`: on each irreducible
component the delta-dimension is the relative dimension at the generic point, which is the
topological dimension of the reduced closed subscheme carried by that component. -/
theorem topologicalKrullDim_le_of_schemeDeltaDimension_le (C : ChowSituation.{u})
    [JacobsonSpace C.S] (hδ : ∀ s : C.S, IsClosed ({s} : Set C.S) → C.dimensionFunction s = 0)
    {X : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f] (n : ℕ)
    (hDim : schemeDeltaDimension C f ≤ (n : EInt)) :
    topologicalKrullDim X ≤ (n : WithBot ℕ∞) := by
  refine topologicalKrullDim_le_of_forall_irreducibleComponents fun W hW => ?_
  let ZW : IrreducibleCloseds X := ⟨W, hW.1, isClosed_of_mem_irreducibleComponents W hW⟩
  rw [schemeDeltaDimension_eq_iSup] at hDim
  have hδW : deltaDimension C f ZW ≤ (n : EInt) :=
    (le_iSup_of_le (⟨W, hW⟩ : irreducibleComponents X) le_rfl).trans hDim
  let I : X.IdealSheafData :=
    Scheme.IdealSheafData.vanishingIdeal ⟨W, isClosed_of_mem_irreducibleComponents W hW⟩
  have hIrange : (Set.range I.subschemeι : Set X) = W := by
    rw [I.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  have : IrreducibleSpace I.subscheme :=
    Scheme.IdealSheafData.irreducibleSpace_subscheme X I (by rw [hIrange]; exact hW.1)
  have : IsIntegral I.subscheme := isIntegral_of_irreducibleSpace_of_isReduced I.subscheme
  have hξ : IsGenericPoint (genericPoint I.subscheme) (Set.univ : Set I.subscheme) :=
    genericPoint_spec I.subscheme
  have hξW : IsGenericPoint (I.subschemeι (genericPoint I.subscheme)) W := by
    rw [isGenericPoint_def, ← Set.image_singleton,
      I.subschemeι.isClosedEmbedding.closure_image_eq, genericPoint_closure, Set.image_univ,
      hIrange]
  have hδeq : deltaDimension C f ZW =
      relativeDimension C.dimensionFunction f (I.subschemeι (genericPoint I.subscheme)) :=
    deltaDimension_eq_of_isGenericPoint C f ZW _ hξW
  have hrel : relativeDimension C.dimensionFunction f
      (I.subschemeι (genericPoint I.subscheme)) ≤ (n : ℤ) := by
    rw [hδeq] at hδW
    exact WithBotTop.coe_le_coe.mp hδW
  have hnonneg := relativeDimension_nonneg C hδ f (I.subschemeι (genericPoint I.subscheme))
  have htop := topologicalKrullDim_eq_relativeDimension_toNat C hδ f I.subschemeι
    (genericPoint I.subscheme) hξ
  have hW' : topologicalKrullDim W = topologicalKrullDim I.subscheme :=
    (IsHomeomorph.topologicalKrullDim_eq _
      (I.subschemeι.isClosedEmbedding.isEmbedding.toHomeomorph.trans
        (Homeomorph.setCongr hIrange)).isHomeomorph).symm
  rw [hW', htop]
  exact_mod_cast show (relativeDimension C.dimensionFunction f
    (I.subschemeι (genericPoint I.subscheme))).toNat ≤ n by omega

/-- Over the spectrum of a field, a bound on the delta-dimension of the support of a coherent
module is a bound on the topological dimension of that support. The spectrum of a field is a
Jacobson space whose Chow dimension function vanishes, and the support of the module is
homeomorphic to the reduced closed subscheme it carries. This is the converse of the conversion
performed by `Stacks.Chow.fiberModule_schemeDeltaDimension_le`. -/
theorem topologicalKrullDim_supp_le_of_field_schemeDeltaDimension_le (k : Type u) [Field k]
    {X : Scheme.{u}} (q : X ⟶ Spec (.of k)) [LocallyOfFiniteType q] (F : X.Modules)
    [F.IsCoherent] (n : ℕ)
    (hDim : schemeDeltaDimension (fieldChowSituation k)
      ((reducedSupport F).subschemeι ≫ q) ≤ (n : EInt)) :
    topologicalKrullDim (SheafOfModules.supp F) ≤ (n : WithBot ℕ∞) := by
  have : JacobsonSpace (fieldChowSituation k).S :=
    inferInstanceAs (JacobsonSpace (Spec (CommRingCat.of k)))
  have hδ : ∀ p : (fieldChowSituation k).S, IsClosed ({p} : Set (fieldChowSituation k).S) →
      (fieldChowSituation k).dimensionFunction p = 0 := fun p _ =>
    fieldChowSituation_dimensionFunction_eq_zero k p
  have htop : topologicalKrullDim (reducedSupport F).subscheme ≤ (n : WithBot ℕ∞) :=
    topologicalKrullDim_le_of_schemeDeltaDimension_le (fieldChowSituation k) hδ
      ((reducedSupport F).subschemeι ≫ q) n hDim
  have hIrange : (Set.range (reducedSupport F).subschemeι : Set X) = SheafOfModules.supp F := by
    rw [Scheme.IdealSheafData.range_subschemeι, coe_support_reducedSupport]
  rw [← IsHomeomorph.topologicalKrullDim_eq _
    ((reducedSupport F).subschemeι.isClosedEmbedding.isEmbedding.toHomeomorph.trans
      (Homeomorph.setCongr hIrange)).isHomeomorph]
  exact htop

/-! ### Transport along an isomorphism of schemes -/

/-- The topological dimension of the support of a module is unchanged by pullback along an
isomorphism of schemes: the support of the pullback is the inverse image of the support, and an
isomorphism of schemes is a homeomorphism. -/
theorem topologicalKrullDim_supp_eq_of_isoPullback {A B : Scheme.{u}} (e : A ≅ B)
    (F : B.Modules) [F.IsFiniteType] (M : A.Modules)
    (h : M ≅ (Scheme.Modules.pullback e.hom).obj F) :
    topologicalKrullDim (SheafOfModules.supp M) =
      topologicalKrullDim (SheafOfModules.supp F) := by
  rw [SheafOfModules.supp_eq_of_iso h, SheafOfModules.supp_pullback]
  exact IsHomeomorph.topologicalKrullDim_eq _
    (e.hom.homeomorph.subtype (p := fun y => y ∈ e.hom ⁻¹' SheafOfModules.supp F)
      (q := fun y => y ∈ SheafOfModules.supp F) fun _ => Iff.rfl).isHomeomorph

/-- **Stacks 02QX** read through an isomorphism. Let `e : A ≅ B` be an isomorphism of schemes
over the base of a Chow situation, let `F` be a coherent `𝒪_B`-module and let `M` be a coherent
`𝒪_A`-module isomorphic to the pullback of `F` along `e`. Then the coefficient of `[M]_k` at a
point of `A` is the coefficient of `[F]_k` at its image in `B`: multiplicity and relative
dimension are both unchanged, an isomorphism of schemes being an open immersion over the base. -/
theorem cycleAssociatedToCoherentSheaf_eq_of_source_iso (C : ChowSituation.{u})
    {A B : Scheme.{u}} (sA : A ⟶ C.S) [LocallyOfFiniteType sA] (sB : B ⟶ C.S)
    [LocallyOfFiniteType sB] (e : A ≅ B) (hbase : e.hom ≫ sB = sA) (M : A.Modules)
    [M.IsCoherent] (F : B.Modules) [F.IsCoherent] (k : ℤ)
    (hMk : schemeDeltaDimension C ((reducedSupport M).subschemeι ≫ sA) ≤ (k : EInt))
    (hFk : schemeDeltaDimension C ((reducedSupport F).subschemeι ≫ sB) ≤ (k : EInt))
    (h : M ≅ (Scheme.Modules.pullback e.hom).obj F) (x : A) :
    (cycleAssociatedToCoherentSheaf C sA M k hMk).1 x =
      (cycleAssociatedToCoherentSheaf C sB F k hFk).1 (e.hom x) := by
  classical
  have : F.IsFiniteType := isFiniteType_of_isCoherent F
  rw [cycleAssociatedToCoherentSheaf_apply, cycleAssociatedToCoherentSheaf_apply,
    SheafOfModules.supp_eq_of_iso h, SheafOfModules.supp_pullback,
    sheafMultiplicity_eq_of_iso h x,
    sheafMultiplicity_pullback_of_isOpenImmersion e.hom F x,
    relativeDimension_eq_of_openImmersion e.hom sB sA hbase C.dimensionFunction x]
  simp only [Set.mem_preimage]

/-! ### The tensor product on a fibre -/

/-- **Stacks 01CD on a fibre.** Let `X --f--> Y --g--> S` and let `s` be a point of `S`. Read on
the base change `X ×_Y Y_s` through the canonical isomorphism `X ×_Y Y_s ≅ X_s`, the module
`F ⊗_{𝒪_X} f^* G` restricted to the fibre `X_s` is the tensor product of the restriction of `F`
with the pullback along `X ×_Y Y_s ⟶ Y_s` of the restriction of `G`: pullback commutes with the
tensor product, and the two ways of pulling `G` back to `X ×_Y Y_s` agree because the square
defining the base change commutes. -/
def fibreTensorPullbackIso {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S) (s : S) (F : X.Modules)
    (G : Y.Modules) :
    (Scheme.Modules.pullback (compFiberIso f g s).hom).obj
        ((Scheme.Modules.pullback ((f ≫ g).fiberι s)).obj (tensorPullback f F G)) ≅
      tensorPullback (pullback.snd f (g.fiberι s))
        ((Scheme.Modules.pullback (pullback.fst f (g.fiberι s))).obj F)
        ((Scheme.Modules.pullback (g.fiberι s)).obj G) := by
  have he : (compFiberIso f g s).hom ≫ (f ≫ g).fiberι s = pullback.fst f (g.fiberι s) :=
    pullbackRightPullbackFstIso_hom_fst g (S.fromSpecResidueField s) f
  have hpull :
      (Scheme.Modules.pullback (pullback.fst f (g.fiberι s))).obj (tensorPullback f F G) ≅
        (Scheme.Modules.pullback (compFiberIso f g s).hom).obj
          ((Scheme.Modules.pullback ((f ≫ g).fiberι s)).obj (tensorPullback f F G)) :=
    ((Scheme.Modules.pullbackCongr he).app (tensorPullback f F G)).symm ≪≫
      ((Scheme.Modules.pullbackComp (compFiberIso f g s).hom
        ((f ≫ g).fiberι s)).app (tensorPullback f F G)).symm
  have hG : (Scheme.Modules.pullback (pullback.fst f (g.fiberι s))).obj
        ((Scheme.Modules.pullback f).obj G) ≅
      (Scheme.Modules.pullback (pullback.snd f (g.fiberι s))).obj
        ((Scheme.Modules.pullback (g.fiberι s)).obj G) :=
    (Scheme.Modules.pullbackComp (pullback.fst f (g.fiberι s)) f).app G ≪≫
      (Scheme.Modules.pullbackCongr
        (pullback.condition (f := f) (g := g.fiberι s))).app G ≪≫
      ((Scheme.Modules.pullbackComp (pullback.snd f (g.fiberι s)) (g.fiberι s)).app G).symm
  have tensorComparison := Stacks.RingedSpace.pullbackTensorIsoApp
    (pullback.fst f (g.fiberι s)).toLRSHom.toShHom F
      ((Scheme.Modules.pullback f).obj G)
  have mappedComparison := ((Functor.uncurry.obj
    (Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨(pullback f (g.fiberι s)).toRingedSpace.presheaf,
        (pullback f (g.fiberι s)).toRingedSpace.IsSheaf⟩) :
      (pullback f (g.fiberι s)).Modules × (pullback f (g.fiberι s)).Modules ⥤
        (pullback f (g.fiberι s)).Modules).mapIso
          (Iso.prod (Iso.refl ((Scheme.Modules.pullback (pullback.fst f (g.fiberι s))).obj F)) hG))
  exact hpull.symm ≪≫ tensorComparison ≪≫ mappedComparison

/-! ### Finiteness of the tensor product with a pullback -/

/-- **Stacks 03L6** for a scheme: the tensor product of two sheaves of modules of finite type is
of finite type. The source statement is for a ringed site, and the ring sheaf of the ringed site
attached to a ringed space is the ring sheaf of that space, so the two hypotheses are re-typed
over the former before it applies. -/
private theorem isFiniteType_tensorSheaf (X : Scheme.{u}) (F G : X.Modules)
    [F.IsFiniteType] [G.IsFiniteType] :
    ((((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj (F)).obj
        (G))).IsFiniteType := by
  have hF : SheafOfModules.IsFiniteType
      (R := (Stacks.SheafOfModules.Tensor.ringSheaf
        (Stacks.Cohomology.SpaceInverseSystems.ringedSiteOfSpace
          X.toRingedSpace).O)) F := ‹F.IsFiniteType›
  have hG : SheafOfModules.IsFiniteType
      (R := (Stacks.SheafOfModules.Tensor.ringSheaf
        (Stacks.Cohomology.SpaceInverseSystems.ringedSiteOfSpace
          X.toRingedSpace).O)) G := ‹G.IsFiniteType›
  exact Stacks.SheafOfModules.TensorLocalProperties.tensorSheaf_isFiniteType
    (Stacks.Cohomology.SpaceInverseSystems.ringedSiteOfSpace X.toRingedSpace) F G

/-- The first observation of the proof of Stacks 0H6L, part one: `F ⊗_{𝒪_X} f^* G` is of finite
type, since `f^* G` is of finite type by Stacks 01B6 and the tensor product of two modules of
finite type is of finite type by Stacks 03L6. -/
instance tensorPullback_isFiniteType {X Y : Scheme.{u}} (f : X ⟶ Y) (F : X.Modules)
    [F.IsFiniteType] (G : Y.Modules) [G.IsFiniteType] : (tensorPullback f F G).IsFiniteType :=
  have : ((Scheme.Modules.pullback f).obj G).IsFiniteType :=
    AlgebraicGeometry.SheafOfModules.pullback_isFiniteType f.toLRSHom.toShHom G
  isFiniteType_tensorSheaf X F ((Scheme.Modules.pullback f).obj G)

/-- The first observation of the proof of Stacks 0H6L, part two: `F ⊗_{𝒪_X} f^* G` is
quasi-coherent, since `f^* G` is quasi-coherent by Stacks 01BG and the tensor product of two
quasi-coherent modules is quasi-coherent by Stacks 01CE. -/
instance tensorPullback_isQuasicoherent {X Y : Scheme.{u}} (f : X ⟶ Y) (F : X.Modules)
    [F.IsQuasicoherent] (G : Y.Modules) [G.IsQuasicoherent] :
    (tensorPullback f F G).IsQuasicoherent :=
  @AlgebraicGeometry.tensorSheaf_isQuasicoherent X.toRingedSpace F
    ((Scheme.Modules.pullback f).obj G) ‹F.IsQuasicoherent›
    (@AlgebraicGeometry.SheafOfModules.modulePullback_isQuasicoherent _ _
      f.toLRSHom.toShHom G ‹G.IsQuasicoherent›)

/-! ### The dimension of the support on a fibre of the composite -/

/-- The base change `X ×_Y Y_s` is locally Noetherian when `f` and `g` are locally of finite
type. -/
private instance pullback_fiberι_isLocallyNoetherian {X Y S : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFiniteType f] (g : Y ⟶ S) [LocallyOfFiniteType g] (s : S) :
    IsLocallyNoetherian (pullback f (g.fiberι s)) :=
  LocallyOfFiniteType.isLocallyNoetherian
    (pullback.snd f (g.fiberι s) ≫ g.fiberToSpecResidueField s)

/-- The pullback to `X ×_Y Y_s` of a module of finite type that is quasi-coherent is coherent. -/
private instance pullback_fst_fiberι_isCoherent {X Y S : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFiniteType f] (g : Y ⟶ S) [LocallyOfFiniteType g] (s : S) (F : X.Modules)
    [F.IsFiniteType] [F.IsQuasicoherent] :
    ((Scheme.Modules.pullback (pullback.fst f (g.fiberι s))).obj F).IsCoherent :=
  Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isQuasicoherent_of_isFiniteType _

/-- The dimension bound of the proof of Stacks 0H6L: on the fibre of `X/S` over `s` the support
of `F ⊗_{𝒪_X} f^* G` has dimension at most `r + e`, so that the family
`[F ⊗_{𝒪_X} f^* G/X/S]_{r + e}` is defined. Read on `X ×_Y Y_s`, the module is the tensor
product of the base change of `F` with the pullback of `G_s`, and that base change has the same
fibrewise dimension bound over `Y_s` as `F` has over `Y`; so Stacks 0H69 bounds the
delta-dimension of its support over `κ(s)` by `r + e`, which is a bound on the topological
dimension. Flatness of `F` is not used. -/
theorem fibreDim_tensorPullback_le {X Y S : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f]
    (g : Y ⟶ S) [LocallyOfFiniteType g] (r e : ℕ) (F : X.Modules) [F.IsFiniteType]
    [F.IsQuasicoherent]
    (hF : ∀ y : Y, topologicalKrullDim
      (SheafOfModules.supp ((Scheme.Modules.pullback (f.fiberι y)).obj F)) ≤ (r : WithBot ℕ∞))
    (G : Y.Modules) [G.IsFiniteType] [G.IsQuasicoherent]
    (hG : ∀ t : S, topologicalKrullDim
      (SheafOfModules.supp ((Scheme.Modules.pullback (g.fiberι t)).obj G)) ≤ (e : WithBot ℕ∞))
    (s : S) :
    topologicalKrullDim (SheafOfModules.supp
        ((Scheme.Modules.pullback ((f ≫ g).fiberι s)).obj (tensorPullback f F G))) ≤
      ((r + e : ℕ) : WithBot ℕ∞) := by
  have hδ := schemeDeltaDimension_tensorPullback_le (fieldChowSituation (S.residueField s))
    (g.fiberToSpecResidueField s) (pullback.snd f (g.fiberι s)) r (e : ℤ)
    ((Scheme.Modules.pullback (pullback.fst f (g.fiberι s))).obj F)
    (supportDimension_le_of_baseChange f (g.fiberι s)
      (fun t => isIso_residueFieldMap_of_isPreimmersion (g.fiberι s) t) F r hF)
    ((Scheme.Modules.pullback (g.fiberι s)).obj G)
    (fiberModule_schemeDeltaDimension_le g G e hG s)
  have hHdim := topologicalKrullDim_supp_le_of_field_schemeDeltaDimension_le
    (S.residueField s) (pullback.snd f (g.fiberι s) ≫ g.fiberToSpecResidueField s)
    (tensorPullback (pullback.snd f (g.fiberι s))
      ((Scheme.Modules.pullback (pullback.fst f (g.fiberι s))).obj F)
      ((Scheme.Modules.pullback (g.fiberι s)).obj G)) (r + e) (by exact_mod_cast hδ)
  rw [← topologicalKrullDim_supp_eq_of_isoPullback (compFiberIso f g s)
    ((Scheme.Modules.pullback ((f ≫ g).fiberι s)).obj (tensorPullback f F G)) _
    (fibreTensorPullbackIso f g s F G).symm]
  exact hHdim

/-! ### The composition of the two associated families -/

/-- **Stacks Project, Tag 0H6L.** Let `f : X ⟶ Y` and `g : Y ⟶ S` be morphisms of schemes, both
locally of finite type, and let `r, e ≥ 0`. Let `F` be a quasi-coherent `𝒪_X`-module of finite
type whose support on every fibre of `f` has dimension at most `r`, and let `G` be a
quasi-coherent `𝒪_Y`-module of finite type whose support on every fibre of `g` has dimension at
most `e`. Set `α = [F/X/Y]_r` and `β = [G/Y/S]_e`. If `F` is flat over `Y` then
`α ∘ β = [F ⊗_{𝒪_X} f^* G/X/S]_{r + e}`. -/
@[stacks 0H6L]
theorem compFamily_familyAssociatedToModule {X Y S : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFiniteType f] (g : Y ⟶ S) [LocallyOfFiniteType g] (r e : ℕ) (F : X.Modules)
    [F.IsFiniteType] [F.IsQuasicoherent]
    (hF : ∀ y : Y, topologicalKrullDim
      (SheafOfModules.supp ((Scheme.Modules.pullback (f.fiberι y)).obj F)) ≤ (r : WithBot ℕ∞))
    (hflat : IsFlatOver f.toLRSHom.toShHom F) (G : Y.Modules) [G.IsFiniteType]
    [G.IsQuasicoherent]
    (hG : ∀ t : S, topologicalKrullDim
      (SheafOfModules.supp ((Scheme.Modules.pullback (g.fiberι t)).obj G)) ≤ (e : WithBot ℕ∞)) :
    compFamily f g r e (familyAssociatedToModule f F r hF)
        (familyAssociatedToModule g G e hG) =
      familyAssociatedToModule (f ≫ g) (tensorPullback f F G) (r + e)
        (fibreDim_tensorPullback_le f g r e F hF G hG) := by
  classical
  funext s
  apply Subtype.ext
  ext x
  have hbase : (compFiberIso f g s).hom ≫ (f ≫ g).fiberToSpecResidueField s =
      pullback.snd f (g.fiberι s) ≫ g.fiberToSpecResidueField s := by
    dsimp only [compFiberIso, Scheme.Hom.fiberToSpecResidueField, Scheme.Hom.fiberι,
      Scheme.Hom.fiber]
    exact pullbackRightPullbackFstIso_hom_snd g (S.fromSpecResidueField s) f
  have hhom : (compFiberIso f g s).hom ((compFiberIso f g s).inv x) = x := by
    simp
  have hsource := cycleAssociatedToCoherentSheaf_eq_of_source_iso
    (fieldChowSituation (S.residueField s))
    (pullback.snd f (g.fiberι s) ≫ g.fiberToSpecResidueField s)
    ((f ≫ g).fiberToSpecResidueField s) (compFiberIso f g s) hbase
    (tensorPullback (pullback.snd f (g.fiberι s))
      ((Scheme.Modules.pullback (pullback.fst f (g.fiberι s))).obj F)
      ((Scheme.Modules.pullback (g.fiberι s)).obj G))
    ((Scheme.Modules.pullback ((f ≫ g).fiberι s)).obj (tensorPullback f F G))
    ((r : ℤ) + (e : ℤ))
    (schemeDeltaDimension_tensorPullback_le (fieldChowSituation (S.residueField s))
      (g.fiberToSpecResidueField s) (pullback.snd f (g.fiberι s)) r (e : ℤ) _
      (supportDimension_le_of_baseChange f (g.fiberι s)
        (fun t => isIso_residueFieldMap_of_isPreimmersion (g.fiberι s) t) F r hF) _
      (fiberModule_schemeDeltaDimension_le g G e hG s))
    (fiberModule_schemeDeltaDimension_le (f ≫ g) (tensorPullback f F G) (r + e)
      (fibreDim_tensorPullback_le f g r e F hF G hG) s)
    (fibreTensorPullbackIso f g s F G).symm ((compFiberIso f g s).inv x)
  rw [hhom] at hsource
  calc (compFamily f g r e (familyAssociatedToModule f F r hF)
        (familyAssociatedToModule g G e hG) s).1 x
      = (cap (fieldChowSituation (S.residueField s)) (g.fiberToSpecResidueField s)
            (pullback.snd f (g.fiberι s))
            (baseChangeFamilyOfResidueIso f (g.fiberι s)
              (fun t => isIso_residueFieldMap_of_isPreimmersion (g.fiberι s) t) r
              (familyAssociatedToModule f F r hF))
            (familyAssociatedToModule g G e hG s)).1 ((compFiberIso f g s).inv x) := rfl
    _ = (cycleAssociatedToCoherentSheaf (fieldChowSituation (S.residueField s))
            (pullback.snd f (g.fiberι s) ≫ g.fiberToSpecResidueField s)
            (tensorPullback (pullback.snd f (g.fiberι s))
              ((Scheme.Modules.pullback (pullback.fst f (g.fiberι s))).obj F)
              ((Scheme.Modules.pullback (g.fiberι s)).obj G)) ((r : ℤ) + (e : ℤ))
            (schemeDeltaDimension_tensorPullback_le (fieldChowSituation (S.residueField s))
              (g.fiberToSpecResidueField s) (pullback.snd f (g.fiberι s)) r (e : ℤ) _
              (supportDimension_le_of_baseChange f (g.fiberι s)
                (fun t => isIso_residueFieldMap_of_isPreimmersion (g.fiberι s) t) F r hF) _
              (fiberModule_schemeDeltaDimension_le g G e hG s))).1
          ((compFiberIso f g s).inv x) := by
          rw [familyAssociatedToModule_baseChange f (g.fiberι s)
              (fun t => isIso_residueFieldMap_of_isPreimmersion (g.fiberι s) t) F r hF,
            familyAssociatedToModule_apply g G e hG s]
          exact congrArg
            (fun z : CycleGroup (fieldChowSituation (S.residueField s))
                (pullback.snd f (g.fiberι s) ≫ g.fiberToSpecResidueField s)
                ((r : ℤ) + (e : ℤ)) => z.1 ((compFiberIso f g s).inv x))
            (cap_familyAssociatedToModule (fieldChowSituation (S.residueField s))
              (g.fiberToSpecResidueField s) (pullback.snd f (g.fiberι s)) r (e : ℤ)
              ((Scheme.Modules.pullback (pullback.fst f (g.fiberι s))).obj F)
              (supportDimension_le_of_baseChange f (g.fiberι s)
                (fun t => isIso_residueFieldMap_of_isPreimmersion (g.fiberι s) t) F r hF)
              (fiberModule_flatOver f g F hflat s)
              ((Scheme.Modules.pullback (g.fiberι s)).obj G)
              (fiberModule_schemeDeltaDimension_le g G e hG s))
    _ = (familyAssociatedToModule (f ≫ g) (tensorPullback f F G) (r + e)
          (fibreDim_tensorPullback_le f g r e F hF G hG) s).1 x := hsource

end Stacks.Chow

end
