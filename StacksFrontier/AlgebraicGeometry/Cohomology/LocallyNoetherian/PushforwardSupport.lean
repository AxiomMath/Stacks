module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CoherenceClosure
public import StacksFrontier.AlgebraicGeometry.Cohomology.Coherent.FiniteTilde
public import StacksFrontier.AlgebraicGeometry.Cohomology.LocallyNoetherian.SliceTransport
public import StacksFrontier.AlgebraicGeometry.AffinePushforward.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.Defs
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CoherentFinitePresentation

/-!
# Coherence of the direct image from an open neighbourhood of the support

Let `U` be an open subscheme of a scheme `X`, let `T ⊆ X` be a closed subset contained in `U`,
and let `F` be a coherent `𝒪_U`-module whose support has image inside `T`. Then the direct image
of `F` along the inclusion of `U` is a coherent `𝒪_X`-module.

The support of a module is `SheafOfModules.supp`, the set of points at which the stalk is
nonzero; the hypothesis is that its image under the open immersion lies in the closed set.

## Main definitions

* `Stacks.AlgebraicGeometry.CoherentPushforward.pushforwardRestrictIso`: the restriction of the
  direct image of `F` to an open `W ≤ U` is the restriction of `F` along the inclusion of `W`
  in `U`.
* `Stacks.AlgebraicGeometry.CoherentPushforward.overEquivFreeIso`, `overEquivFreeInverseIso` and
  `restrictFreeIso`: the comparison isomorphisms expressing that the three transports used here
  take free modules to free modules.

## Main results

* `Stacks.AlgebraicGeometry.CoherentPushforward.isCoherent_pushforward_of_supp_subset`: the
  direct image of a coherent module supported inside a closed subset contained in the open is
  coherent.
* `Stacks.AlgebraicGeometry.CoherentPushforward.isCoherentOn_pushforward`: the direct image is
  coherent on the open it comes from.
* `Stacks.AlgebraicGeometry.CoherentPushforward.isCoherentOn_pushforward_of_notMem`: the direct
  image is coherent on every open disjoint from a set containing the image of the support.
* `Stacks.AlgebraicGeometry.CoherentPushforward.isFiniteType_overEquiv_functor`: being of finite
  type transports from the slice site at an open to the corresponding open subscheme. The
  converse direction is
  `Stacks.AlgebraicGeometry.CoherentTFAE.isFiniteType_overEquiv_inverse`.
* `Stacks.AlgebraicGeometry.CoherentPushforward.preservesKernel_restrictFunctor`: restriction
  along an open immersion of schemes preserves kernels.
* `Stacks.AlgebraicGeometry.CoherentPushforward.isFiniteType_kernel_free_over`: over an open
  contained in `U`, the kernel of a map from a finite free module into the direct image is of
  finite type.
* `Stacks.AlgebraicGeometry.CoherentPushforward.isZero_pushforward_over_of_notMem`: the direct
  image vanishes on every open missing a set containing the image of the support.

## References

* [Stacks Project, Tag 0CYJ](https://stacks.math.columbia.edu/tag/0CYJ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.CoherentPushforward

/-! ### Transport of finite type across the slice comparison -/

/-- **Finite type transports from the slice site at an open to the open subscheme.** A module of
finite type on the slice site of the opens of `X` at `U` is of finite type as a module on the
scheme `U`, under `Scheme.Modules.overEquiv`. -/
theorem isFiniteType_overEquiv_functor {X : Scheme.{u}} (U : X.Opens)
    (M : SheafOfModules (X.ringCatSheaf.over U)) (hM : M.IsFiniteType) :
    ((Scheme.Modules.overEquiv U).functor.obj M).IsFiniteType :=
  @Stacks.SheafOfModules.isFiniteType_pushforward _ _ _ _ _ _ _ _ _ _ _ _ _ _
    U.overEquivalence.inverse _ _ _ _
    (U.overPullbackSheafEquivOver.app X.ringCatSheaf).inv (Iso.isIso_inv _)
    (U.sheafOfModulesEquivOverUnit X.ringCatSheaf) M hM

/-! ### Free modules under the three transports -/

/-- `Scheme.Modules.overEquiv` carries a free module on the slice site at `U` to a free module on
the scheme `U`. -/
noncomputable def overEquivFreeIso {X : Scheme.{u}} (U : X.Opens) (I : Type u) :
    (SheafOfModules.free I : (U : Scheme.{u}).Modules) ≅
      (Scheme.Modules.overEquiv U).functor.obj (SheafOfModules.free I) :=
  have hpres : PreservesColimitsOfShape.{u, u} (Discrete I)
      (Scheme.Modules.overEquiv U).functor :=
    Functor.instPreservesColimitsOfShapeOfIsLeftAdjoint.{u, u, u, u + 1, u, u + 1} _
  @SheafOfModules.mapFreeIso _ _ _ _ _ _ _ _ _ _ _ _
    (Scheme.Modules.overEquiv U).functor I hpres
    (U.sheafOfModulesEquivOverUnit X.ringCatSheaf).symm

/-- The inverse of `Scheme.Modules.overEquiv` carries a free module on the scheme `U` to a free
module on the slice site at `U`. -/
noncomputable def overEquivFreeInverseIso {X : Scheme.{u}} (U : X.Opens) (I : Type u) :
    (SheafOfModules.free I : SheafOfModules (X.ringCatSheaf.over U)) ≅
      (Scheme.Modules.overEquiv U).inverse.obj (SheafOfModules.free I) :=
  have hpres : PreservesColimitsOfShape.{u, u} (Discrete I)
      (Scheme.Modules.overEquiv U).inverse :=
    Functor.instPreservesColimitsOfShapeOfIsLeftAdjoint.{u, u, u, u + 1, u, u + 1} _
  @SheafOfModules.mapFreeIso _ _ _ _ _ _ _ _ _ _ _ _
    (Scheme.Modules.overEquiv U).inverse I hpres
    (AffinePushforward.overInverseUnitIso U)

/-- Restriction along an open immersion of schemes carries a free module to a free module. -/
noncomputable def restrictFreeIso {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    (I : Type u) :
    (SheafOfModules.free I : X.Modules) ≅
      (Scheme.Modules.restrictFunctor f).obj (SheafOfModules.free I) :=
  have hpres : PreservesColimitsOfShape.{u, u} (Discrete I)
      (Scheme.Modules.restrictFunctor f) :=
    Functor.instPreservesColimitsOfShapeOfIsLeftAdjoint.{u, u, u, u + 1, u, u + 1} _
  @SheafOfModules.mapFreeIso _ _ _ _ _ _ _ _ _ _ _ _
    (Scheme.Modules.restrictFunctor f) I hpres
    (Scheme.Modules.restrictUnitIso f).symm

/-- **Restriction along an open immersion of schemes preserves kernels.** -/
theorem preservesKernel_restrictFunctor {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    {M N : Y.Modules} (ψ : M ⟶ N) :
    PreservesLimit (parallelPair ψ 0) (Scheme.Modules.restrictFunctor f) := by
  dsimp only [Scheme.Modules.restrictFunctor]
  exact Stacks.SheafOfModules.FiniteTypeKernel.preservesLimitPushforward _ _

/-! ### The direct image on a smaller open -/

/-- **The direct image of `F` along an open immersion, restricted to a smaller open, is a
restriction of `F`.** For `W ≤ U` the restriction of the direct image of `F` to `W` is the
restriction of `F` along the inclusion of `W` in `U`. -/
noncomputable def pushforwardRestrictIso {X : Scheme.{u}} (U W : X.Opens) (hWU : W ≤ U)
    (F : (U : Scheme.{u}).Modules) :
    ((Scheme.Modules.pushforward U.ι).obj F).restrict W.ι ≅ F.restrict (X.homOfLE hWU) :=
  have hcomp : X.homOfLE hWU ≫ U.ι = W.ι := by simp
  (Scheme.Modules.restrictFunctorCongr hcomp).symm.app _ ≪≫
    (Scheme.Modules.restrictFunctorComp (X.homOfLE hWU) U.ι).app _ ≪≫
    (Scheme.Modules.restrictFunctor (X.homOfLE hWU)).mapIso
      ((Scheme.Modules.restrictFunctorAdjCounitIso U.ι).app F)

/-- **The direct image is of finite type on every open contained in the open it comes from.** -/
theorem isFiniteType_pushforward_over_of_le {X : Scheme.{u}} (U W : X.Opens) (hWU : W ≤ U)
    (F : (U : Scheme.{u}).Modules) (hF : F.IsFiniteType) :
    (((Scheme.Modules.pushforward U.ι).obj F).over W).IsFiniteType := by
  have h₁ : (F.restrict (X.homOfLE hWU)).IsFiniteType :=
    have := hF
    CoherentTFAE.isFiniteType_restrict (X.homOfLE hWU) F
  have h₂ : (((Scheme.Modules.pushforward U.ι).obj F).restrict W.ι).IsFiniteType :=
    have := h₁
    Stacks.SheafOfModules.isFiniteType_of_iso.{u} (pushforwardRestrictIso U W hWU F).symm
  have h₃ : ((Scheme.Modules.overEquiv W).inverse.obj
      (((Scheme.Modules.pushforward U.ι).obj F).restrict W.ι)).IsFiniteType :=
    have := h₂
    CoherentTFAE.isFiniteType_overEquiv_inverse W _
  exact Stacks.SheafOfModules.isFiniteType_of_iso.{u}
    (M := (Scheme.Modules.overEquiv W).inverse.obj
      (((Scheme.Modules.pushforward U.ι).obj F).restrict W.ι))
    (N := ((Scheme.Modules.pushforward U.ι).obj F).over W)
    (AffinePushforward.overInverseIso W ((Scheme.Modules.pushforward U.ι).obj F)).symm

/-! ### Kernels of maps out of finite free modules into a coherent module -/

/-- The kernel of a map `ψ` conjugated by isomorphisms is the image of the kernel of `ψ` under a
functor preserving it. -/
private noncomputable def kernel_conj_iso_obj_kernel {C D : Type*} [Category C] [Category D]
    [HasZeroMorphisms C] [HasZeroMorphisms D] (G : C ⥤ D) {A B : C} {A' B' : D} (ψ : A ⟶ B)
    (eA : A' ≅ G.obj A) (eB : G.obj B ≅ B') [HasKernel ψ] [HasKernel (G.map ψ)]
    [G.PreservesZeroMorphisms] [PreservesLimit (parallelPair ψ 0) G] :
    kernel (eA.hom ≫ G.map ψ ≫ eB.hom) ≅ G.obj (kernel ψ) :=
  have := Iso.isIso_hom eA
  kernelIsIsoComp eA.hom (G.map ψ ≫ eB.hom) ≪≫ kernelCompMono (G.map ψ) eB.hom ≪≫
    (PreservesKernel.iso G ψ).symm

/-- **The kernel of a map from a finite free module into the restriction of a coherent module to
an open subscheme is of finite type.** -/
theorem isFiniteType_kernel_free_restrict {X : Scheme.{u}} (F : X.Modules) [F.IsCoherent]
    (A : X.Opens) {I : Type u} [Finite I]
    (ψ : (SheafOfModules.free I : (A : Scheme.{u}).Modules) ⟶ F.restrict A.ι) :
    (kernel ψ).IsFiniteType := by
  let E := Scheme.Modules.overEquiv A
  let eFree := overEquivFreeInverseIso A I
  let eTarget : E.inverse.obj (F.restrict A.ι) ≅ F.over A :=
    E.inverse.mapIso ((Scheme.Modules.overFunctorEquiv A).app F).symm ≪≫
      (E.unitIso.app (F.over A)).symm
  have hker : (kernel (eFree.hom ≫ E.inverse.map ψ ≫ eTarget.hom)).IsFiniteType :=
    _root_.SheafOfModules.IsCoherent.kernel_isFiniteType (M := F) A I inferInstance _
  have hInv : (E.inverse.obj (kernel ψ)).IsFiniteType :=
    have := hker
    Stacks.SheafOfModules.isFiniteType_of_iso.{u}
      (M := kernel (eFree.hom ≫ E.inverse.map ψ ≫ eTarget.hom))
      (N := E.inverse.obj (kernel ψ)) (kernel_conj_iso_obj_kernel E.inverse ψ eFree eTarget)
  have hFun : (E.functor.obj (E.inverse.obj (kernel ψ))).IsFiniteType :=
    isFiniteType_overEquiv_functor A _ hInv
  exact Stacks.SheafOfModules.isFiniteType_of_iso.{u}
    (M := E.functor.obj (E.inverse.obj (kernel ψ))) (N := kernel ψ)
    (E.counitIso.app (kernel ψ))

/-- **The kernel of a map from a finite free module into the restriction of a coherent module
along the inclusion of a smaller open is of finite type.** -/
theorem isFiniteType_kernel_free_restrict_homOfLE {X : Scheme.{u}} (U W : X.Opens) (hWU : W ≤ U)
    (F : (U : Scheme.{u}).Modules) [F.IsCoherent] {I : Type u} [Finite I]
    (ψ : (SheafOfModules.free I : (W : Scheme.{u}).Modules) ⟶ F.restrict (X.homOfLE hWU)) :
    (kernel ψ).IsFiniteType := by
  let A := U.ι ⁻¹ᵁ W
  let e : (A : Scheme.{u}) ≅ (W : Scheme.{u}) := Scheme.Opens.isoOfLE hWU
  have he : e.hom ≫ X.homOfLE hWU = A.ι := by
    refine (cancel_mono U.ι).mp ?_
    simp only [Category.assoc, Scheme.homOfLE_ι]
    exact Scheme.Opens.isoOfLE_hom_ι hWU
  let H := Scheme.Modules.restrictFunctor e.hom
  have hH := preservesKernel_restrictFunctor e.hom ψ
  let eTarget : H.obj (F.restrict (X.homOfLE hWU)) ≅ F.restrict A.ι :=
    ((Scheme.Modules.restrictFunctorComp e.hom (X.homOfLE hWU)).app F).symm ≪≫
      (Scheme.Modules.restrictFunctorCongr he).app F
  let eFree := restrictFreeIso e.hom I
  have hker : (kernel (eFree.hom ≫ H.map ψ ≫ eTarget.hom)).IsFiniteType :=
    isFiniteType_kernel_free_restrict F A _
  have hHker : ((Scheme.Modules.restrictFunctor e.hom).obj (kernel ψ)).IsFiniteType :=
    have := hker
    Stacks.SheafOfModules.isFiniteType_of_iso.{u}
      (M := kernel (eFree.hom ≫ H.map ψ ≫ eTarget.hom))
      (N := (Scheme.Modules.restrictFunctor e.hom).obj (kernel ψ))
      (kernel_conj_iso_obj_kernel H ψ eFree eTarget)
  have hBack : ((Scheme.Modules.restrictFunctor e.inv).obj
      ((Scheme.Modules.restrictFunctor e.hom).obj (kernel ψ))).IsFiniteType :=
    have := hHker
    CoherentTFAE.isFiniteType_restrict e.inv
      ((Scheme.Modules.restrictFunctor e.hom).obj (kernel ψ))
  exact Stacks.SheafOfModules.isFiniteType_of_iso.{u}
    (M := (Scheme.Modules.restrictFunctor e.inv).obj
      ((Scheme.Modules.restrictFunctor e.hom).obj (kernel ψ)))
    (N := kernel ψ)
    (((Scheme.Modules.restrictFunctorComp e.inv e.hom).app (kernel ψ)).symm ≪≫
      (Scheme.Modules.restrictFunctorCongr e.inv_hom_id).app (kernel ψ) ≪≫
      Scheme.Modules.restrictFunctorId.app (kernel ψ))

/-- **The second condition of coherence for the direct image, over an open contained in the open
it comes from.** For `W ≤ U` and a finite free module on the slice site at `W`, the kernel of any
map into the restriction of the direct image to `W` is of finite type. -/
theorem isFiniteType_kernel_free_over {X : Scheme.{u}} (U W : X.Opens) (hWU : W ≤ U)
    (F : (U : Scheme.{u}).Modules) [F.IsCoherent] {I : Type u} [Finite I]
    (φ : (SheafOfModules.free I : SheafOfModules (X.ringCatSheaf.over W)) ⟶
      ((Scheme.Modules.pushforward U.ι).obj F).over W) :
    (kernel φ).IsFiniteType := by
  let E := Scheme.Modules.overEquiv W
  let eFree := overEquivFreeIso W I
  let eTarget := (Scheme.Modules.overFunctorEquiv W).app
      ((Scheme.Modules.pushforward U.ι).obj F) ≪≫ pushforwardRestrictIso U W hWU F
  have hker : (kernel (eFree.hom ≫ E.functor.map φ ≫ eTarget.hom)).IsFiniteType :=
    isFiniteType_kernel_free_restrict_homOfLE U W hWU F _
  have hK : (E.functor.obj (kernel φ)).IsFiniteType :=
    have := hker
    Stacks.SheafOfModules.isFiniteType_of_iso.{u}
      (M := kernel (eFree.hom ≫ E.functor.map φ ≫ eTarget.hom))
      (N := E.functor.obj (kernel φ)) (kernel_conj_iso_obj_kernel E.functor φ eFree eTarget)
  have hInv : (E.inverse.obj (E.functor.obj (kernel φ))).IsFiniteType :=
    have := hK
    CoherentTFAE.isFiniteType_overEquiv_inverse W _
  exact Stacks.SheafOfModules.isFiniteType_of_iso.{u}
    (M := E.inverse.obj (E.functor.obj (kernel φ))) (N := kernel φ)
    (E.unitIso.app (kernel φ)).symm

/-! ### Vanishing away from the support -/

/-- A section of a sheaf of modules over an open at all of whose points the stalk vanishes is
zero. -/
theorem eq_zero_of_forall_stalk_eq_zero {X : TopCat.{u}} {R : TopCat.Sheaf RingCat.{u} X}
    (M : SheafOfModules.{u} R) (W : Opens X) (s : M.val.presheaf.obj (.op W))
    (h : ∀ x ∈ W, ∀ a : (show TopCat.Presheaf AddCommGrpCat.{u} X from M.val.presheaf).stalk x,
      a = 0) :
    s = 0 := by
  classical
  let P : TopCat.Presheaf AddCommGrpCat.{u} X := M.val.presheaf
  have hlocal (x : {x : X // x ∈ W}) :
      ∃ (V : Opens X) (f : V ⟶ W), x.1 ∈ V ∧ P.map f.op s = 0 := by
    obtain ⟨V, hxV, f, g, heq⟩ := TopCat.Presheaf.germ_eq P x.1 x.2 x.2 s 0
      (by simpa using h x.1 x.2 ((P.germ W x.1 x.2) s))
    exact ⟨V, f, hxV, by simpa using heq⟩
  choose V f hxV hzero using hlocal
  have hS : Sieve.ofArrows V f ∈ Opens.grothendieckTopology X W := by
    rw [Opens.mem_grothendieckTopology]
    intro x hx
    exact ⟨V ⟨x, hx⟩, f ⟨x, hx⟩, Sieve.ofArrows_mk V f ⟨x, hx⟩, hxV ⟨x, hx⟩⟩
  refine M.isSheaf.isSeparated W _ hS s 0 fun Y g hg => ?_
  change P.map g.op s = P.map g.op 0
  rcases hg with ⟨Z, k, _, ⟨y⟩, rfl⟩
  simp only [op_comp, P.map_comp, ConcreteCategory.comp_apply]
  rw [hzero y]
  simp

/-- A section of `F` over an open of `U` whose image misses `T` is zero, when the image of the
support of `F` lies in `T`. -/
theorem restrict_section_eq_zero_of_notMem {X : Scheme.{u}} (U : X.Opens) (T : Set X)
    (F : (U : Scheme.{u}).Modules) (hF : U.ι.base '' SheafOfModules.supp F ⊆ T)
    (W : Opens (U : Scheme.{u}).toTopCat) (s : F.val.presheaf.obj (.op W))
    (hW : ∀ x ∈ W, U.ι.base x ∉ T) : s = 0 := by
  refine eq_zero_of_forall_stalk_eq_zero F W s fun x hx a => ?_
  by_contra ha
  exact hW x hx (hF ⟨x, ⟨a, ha⟩, rfl⟩)

/-- A section of the direct image of `F` over an open missing `T` is zero. -/
theorem pushforward_section_eq_zero_of_notMem {X : Scheme.{u}} (U : X.Opens) (T : Set X)
    (F : (U : Scheme.{u}).Modules) (hF : U.ι.base '' SheafOfModules.supp F ⊆ T) (W : Opens X)
    (s : ((Scheme.Modules.pushforward U.ι).obj F).presheaf.obj (.op W))
    (hW : ∀ x ∈ W, x ∉ T) : s = 0 :=
  restrict_section_eq_zero_of_notMem U T F hF (U.ι ⁻¹ᵁ W) s fun x hx => hW (U.ι.base x) hx

/-- **The direct image vanishes away from the support.** The restriction of the direct image of
`F` to the slice site at an open missing `T` is a zero object. -/
theorem isZero_pushforward_over_of_notMem {X : Scheme.{u}} (U : X.Opens) (T : Set X)
    (F : (U : Scheme.{u}).Modules) (hF : U.ι.base '' SheafOfModules.supp F ⊆ T) (V : X.Opens)
    (hV : ∀ x ∈ V, x ∉ T) :
    IsZero (((Scheme.Modules.pushforward U.ι).obj F).over V) := by
  refine (IsZero.iff_id_eq_zero _).mpr ?_
  ext W s
  change s = 0
  exact pushforward_section_eq_zero_of_notMem U T F hF W.unop.left s
    fun x hx => hV x ((leOfHom W.unop.hom) hx)

/-! ### Coherence on the two members of the cover -/

/-- **The direct image is coherent on the open it comes from.** -/
theorem isCoherentOn_pushforward {X : Scheme.{u}} (U : X.Opens)
    (F : (U : Scheme.{u}).Modules) [F.IsCoherent] :
    Stacks.SheafOfModules.IsCoherentOn ((Scheme.Modules.pushforward U.ι).obj F) U := by
  intro W hWU
  refine ⟨isFiniteType_pushforward_over_of_le U W hWU F
      _root_.SheafOfModules.IsCoherent.isFiniteType, fun N σ hσ g => ?_⟩
  have := hσ
  exact Stacks.SheafOfModules.isFiniteType_kernel_of_epi_comp σ.π g
    (isFiniteType_kernel_free_over U W hWU F (σ.π ≫ g))

/-- **The direct image is coherent on every open missing a set containing the image of the
support.** -/
theorem isCoherentOn_pushforward_of_notMem {X : Scheme.{u}} (U : X.Opens) (T : Set X)
    (F : (U : Scheme.{u}).Modules) (hF : U.ι.base '' SheafOfModules.supp F ⊆ T) (V : X.Opens)
    (hV : ∀ x ∈ V, x ∉ T) :
    Stacks.SheafOfModules.IsCoherentOn ((Scheme.Modules.pushforward U.ι).obj F) V := by
  intro W hWV
  have hzero := isZero_pushforward_over_of_notMem U T F hF W fun x hx => hV x (hWV hx)
  refine ⟨Stacks.SheafOfModules.isFiniteType_of_isZero.{u} hzero, fun N σ hσ g => ?_⟩
  have hσ' : σ.IsFiniteType := ⟨hσ⟩
  have hN : N.IsFiniteType := Stacks.SheafOfModules.isFiniteType_of_generatingSections.{u} σ
  rw [hzero.eq_zero_of_tgt g]
  exact Stacks.SheafOfModules.isFiniteType_of_iso.{u} (M := N)
    (N := kernel (0 : N ⟶ ((Scheme.Modules.pushforward U.ι).obj F).over W))
    kernelZeroIsoSource.symm

/-! ### The main theorem -/

/-- A coherent sheaf on an open subscheme, supported on a closed subset contained in
that open, has coherent direct image. -/
@[stacks 0CYJ]
theorem isCoherent_pushforward_of_supp_subset {X : Scheme.{u}} (U : X.Opens) (T : Set X)
    (hT : IsClosed T) (hTU : T ⊆ U)
    (F : (U : Scheme.{u}).Modules) [F.IsCoherent]
    (hF : U.ι.base '' SheafOfModules.supp F ⊆ T) :
    ((Scheme.Modules.pushforward U.ι).obj F).IsCoherent := by
  let V : X.Opens := ⟨Tᶜ, hT.isOpen_compl⟩
  let Xc : ULift.{u} Bool → X.Opens := fun b => if b.down then V else U
  have hcover : (Opens.grothendieckTopology (X : Type u)).CoversTop Xc := by
    refine (Opens.coversTop_iff (X : Type u) Xc).2 ?_
    change (⨆ b, Xc b) = ⊤
    rw [iSup_ulift, iSup_bool_eq]
    change V ⊔ U = ⊤
    ext x
    change (x ∈ V ∨ x ∈ U) ↔ True
    exact ⟨fun _ => trivial, fun _ => (em (x ∈ T)).elim (fun hx => Or.inr (hTU hx)) Or.inl⟩
  have hloc : ∀ b, Stacks.SheafOfModules.IsCoherentOn
      ((Scheme.Modules.pushforward U.ι).obj F) (Xc b) := by
    rintro ⟨b⟩
    cases b with
    | false => simpa [Xc] using isCoherentOn_pushforward U F
    | true =>
      simpa [Xc] using isCoherentOn_pushforward_of_notMem U T F hF V fun _ hx => hx
  have h := Stacks.SheafOfModules.isCoherent_of_coversTop
    ((Scheme.Modules.pushforward U.ι).obj F) Xc hcover hloc
  exact ⟨h.isFiniteType, h.kernel_isFiniteType⟩

end Stacks.AlgebraicGeometry.CoherentPushforward

end
