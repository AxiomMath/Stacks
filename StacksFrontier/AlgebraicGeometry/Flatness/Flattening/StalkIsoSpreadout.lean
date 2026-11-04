module

public import StacksFrontier.AlgebraicGeometry.Modules.FinitePresentationPullbackScheme
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorExactnessSheafify
public import StacksFrontier.AlgebraicGeometry.CoherentTFAE.Basic
public import StacksFrontier.AlgebraicGeometry.DerivedAcyclic.Pushforward
public import StacksFrontier.AlgebraicGeometry.DevissageNoetherian.Support
public import StacksFrontier.AlgebraicGeometry.FiniteTypeSubmodule.KernelGlue
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.PullbackStalk
public import StacksFrontier.AlgebraicGeometry.Flatness.Devissage.OneStep.FreeMap
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.StrictTransformFlatnessShortExact
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.ReflectIso
public import StacksFrontier.AlgebraicGeometry.Modules.StalkSupport
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.PullbackSkyscraper
public import StacksFrontier.Topology.Sheaves.Modules.FiniteType
import StacksFrontier.AlgebraicGeometry.Modules.StalkFreePullback

/-!
# From one stalk to a neighbourhood: the isomorphism steps of the flattening theorem

The core induction step of [Stacks, Tag 0815] produces a map `α : 𝒪ʳ ⟶ ℱ` which is known to be
an isomorphism only after pullback along the residue field at a single point. This module
upgrades that to an isomorphism on an open neighbourhood, and transports an isomorphism on an
open neighbourhood along any morphism whose image lies inside it.

**Residue field to stalk.** Surjectivity of the stalk map is Nakayama: the cokernel of `α` has
no support at the point (`AlgebraicGeometry.notMem_supp_cokernel_of_isIso`), which is exactly
surjectivity on the stalk there
(`AlgebraicGeometry.Scheme.Modules.surjective_stalkLinearMap_iff_notMem_supp_cokernel`).
Injectivity is the determinant trick — a surjection between free modules of the same finite rank
over a commutative ring is injective — and the two ranks agree because by [Stacks, Tag 0098] the
stalk of a pullback is the base change of the stalk, so both are read off the residue-field
fibre.

**Stalk to neighbourhood.** The stalk functor on modules is exact, so it carries the cokernel and
the kernel of `α` to the cokernel and kernel of the stalk map; an isomorphism on the stalk at `x`
therefore makes both vanish at `x`. Since the support of a module of finite type is closed, the
cokernel vanishes on the open complement of its support, which makes `α` an epimorphism there,
and the kernel vanishes on the open complement of *its* support; pullback along an open immersion
is exact, so on that second open both the pulled-back kernel and the pulled-back cokernel are
zero and `α` becomes an isomorphism. This is part (4) of [Stacks, Tag 01Y3] with finite
presentation in place of coherence, which is what Tag 0815 has available: the kernel is of finite
type because it is the kernel of an epimorphism from a module of finite type onto a module of
finite presentation ([Stacks, Tag 01BP] part (2)), not because the target is coherent.

## Main results

* `AlgebraicGeometry.isIso_stalk_of_isIso_residuePullback`: **an isomorphism over the residue
  field at `x` is an isomorphism on stalks at `x`**, for a map between modules with finite free
  stalks there.
* `AlgebraicGeometry.exists_isIso_pullback_open_of_stalk_isIso_on_open`: **an isomorphism on one
  stalk is an isomorphism on a neighbourhood**, given finite presentation of the target over an
  open containing the point.
* `AlgebraicGeometry.isIso_pullback_map_of_range_le`: a morphism of modules which is an
  isomorphism on an open pulls back to an isomorphism along every morphism with image in that
  open.

## Implementation notes

The hypotheses on the stalks of the source and target in
`AlgebraicGeometry.isIso_stalk_of_isIso_residuePullback` are freeness and finiteness as modules
over the local ring, rather than local freeness of the sheaves: in the application the source is
a finite free module and the target's stalk is known to be free only at the one point in
question, which is where the flattening induction has arranged it.

`AlgebraicGeometry.Scheme.Modules` carries copies of the categorical instances of
`SheafOfModules`, so an `Epi` in one reading is invisible to instance search in the other;
`AlgebraicGeometry.Scheme.Modules.epi_sheafOfModules` transports it where [Stacks, Tag 01BP] is
applied.

## References

* [Stacks Project, Tag 0815](https://stacks.math.columbia.edu/tag/0815)
* [Stacks Project, Tag 01Y3](https://stacks.math.columbia.edu/tag/01Y3)
* [Stacks Project, Tag 01BP](https://stacks.math.columbia.edu/tag/01BP)
* [Stacks Project, Tag 0098](https://stacks.math.columbia.edu/tag/0098)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-! ### Transporting an isomorphism on an open -/

/-- **A morphism of modules which is an isomorphism on an open pulls back to an isomorphism
along every morphism with image in that open.** Such a morphism factors through the open
immersion, and pullback along a composite inverts whatever pullback along the second factor
inverts. -/
theorem isIso_pullback_map_of_range_le {X T : Scheme.{u}} {G F : X.Modules}
    (α : G ⟶ F) (W : X.Opens) (hαW : IsIso ((Scheme.Modules.pullback W.ι).map α))
    (k : T ⟶ X) (hk : Set.range k.base ⊆ (W : Set X)) :
    IsIso ((Scheme.Modules.pullback k).map α) := by
  have hr : Set.range k.base ⊆ Set.range W.ι.base := by
    rwa [Scheme.Opens.range_ι]
  exact (Stacks.AlgebraicGeometry.ModuleLimits.isIso_pullback_map_comp_iff
      (IsOpenImmersion.lift W.ι k hr) W.ι k (IsOpenImmersion.lift_fac W.ι k hr) α).mp
    (Functor.map_isIso (Scheme.Modules.pullback (IsOpenImmersion.lift W.ι k hr)) _)

/-! ### From a residue-field isomorphism to a stalk isomorphism -/

/-- **Nakayama on stalks.** A morphism with target of finite type whose pullback along the
residue field at `x` is an isomorphism is surjective on stalks at `x`: the cokernel has no
support at `x`, which is exactly surjectivity of the stalk map there. -/
private theorem surjective_stalkLinearMap_of_isIso_residuePullback
    {X : Scheme.{u}} {G F : X.Modules} (α : G ⟶ F) [F.IsFiniteType] (x : X)
    (hα : IsIso ((Scheme.Modules.pullback (X.fromSpecResidueField x)).map α)) :
    Function.Surjective (stalkLinearMap G F α x) :=
  have : (cokernel α).IsFiniteType := Scheme.Modules.isFiniteType_cokernel α inferInstance
  (Scheme.Modules.surjective_stalkLinearMap_iff_notMem_supp_cokernel α x).mpr
    (notMem_supp_cokernel_of_isIso α x hα)

/-- A morphism with free stalks whose pullback along the residue field at `x` is an isomorphism
has stalks of the same rank at `x`: both ranks are the rank of the residue-field fibre. -/
private theorem finrank_stalk_eq_of_isIso_residuePullback
    {X : Scheme.{u}} {G F : X.Modules} (α : G ⟶ F) (x : X)
    (hG : Module.Free (X.presheaf.stalk x) (G.presheaf.stalk x))
    (hF : Module.Free (X.presheaf.stalk x) (F.presheaf.stalk x))
    (hα : IsIso ((Scheme.Modules.pullback (X.fromSpecResidueField x)).map α)) :
    Module.finrank (X.presheaf.stalk x) (G.presheaf.stalk x) =
      Module.finrank (X.presheaf.stalk x) (F.presheaf.stalk x) := by
  let p := X.fromSpecResidueField x
  let c : (Spec (.of (X.residueField x)) : Scheme.{u}) :=
    IsLocalRing.closedPoint (X.residueField x)
  have hpc : p c = x := Scheme.fromSpecResidueField_apply x _
  have : IsIso ((Scheme.Modules.pullback p).map α) := hα
  rw [← Stacks.StalkFreeBridge.finrank_stalk_pullback p G c x hpc hG,
    ← Stacks.StalkFreeBridge.finrank_stalk_pullback p F c x hpc hF]
  exact LinearEquiv.finrank_eq
    (schemeStalkLinearEquiv (asIso ((Scheme.Modules.pullback p).map α)) c)

/-- **An isomorphism over the residue field at `x` is an isomorphism on stalks at `x`.**
Surjectivity is Nakayama, and a surjection between finite free modules of equal rank over a
commutative ring is injective. -/
theorem isIso_stalk_of_isIso_residuePullback
    {X : Scheme.{u}} {G F : X.Modules} (α : G ⟶ F) [F.IsFiniteType] (x : X)
    (hGfree : Module.Free (X.presheaf.stalk x) (G.presheaf.stalk x))
    (hGfin : Module.Finite (X.presheaf.stalk x) (G.presheaf.stalk x))
    (hFfree : Module.Free (X.presheaf.stalk x) (F.presheaf.stalk x))
    (hFfin : Module.Finite (X.presheaf.stalk x) (F.presheaf.stalk x))
    (hα : IsIso ((Scheme.Modules.pullback (X.fromSpecResidueField x)).map α)) :
    IsIso ((Scheme.Modules.toPresheaf X ⋙
      TopCat.Presheaf.stalkFunctor Ab.{u} x).map α) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  exact OrzechProperty.bijective_of_surjective_of_finrank_le (stalkLinearMap G F α x)
    (surjective_stalkLinearMap_of_isIso_residuePullback α x hα)
    (finrank_stalk_eq_of_isIso_residuePullback α x hGfree hFfree hα).le

/-! ### From a stalk isomorphism to an isomorphism on a neighbourhood -/

/-- The pullback of a module of finite type to an open disjoint from its support is zero: by
[Stacks, Tag 056J] the support of the pullback is the preimage of the support, which is empty. -/
private theorem pullback_isZero_of_disjoint_supp_open {X : Scheme.{u}}
    (F : X.Modules) [F.IsFiniteType] (V : X.Opens)
    (hV : Disjoint (V : Set X) (SheafOfModules.supp F)) :
    IsZero ((Scheme.Modules.pullback V.ι).obj F) := by
  apply Stacks.AlgebraicGeometry.DevissageNoetherian.isZero_of_supp_eq_empty
  rw [Stacks.Modules.supp_pullback]
  exact Set.eq_empty_iff_forall_notMem.mpr fun z hz => Set.disjoint_left.mp hV z.property hz

/-- A morphism of modules whose cokernel pulls back to zero on an open `V` is an epimorphism after
pullback to `V`. -/
private theorem epi_pullback_map_of_isZero_pullback_cokernel {X : Scheme.{u}} {G F : X.Modules}
    (α : G ⟶ F) (V : X.Opens) (h : IsZero ((Scheme.Modules.pullback V.ι).obj (cokernel α))) :
    Epi ((Scheme.Modules.pullback V.ι).map α) :=
  Abelian.epi_of_cokernel_π_eq_zero _
    ((h.of_iso (PreservesCokernel.iso (Scheme.Modules.pullback V.ι) α).symm).eq_of_tgt _ _)

/-- **Surjectivity on one stalk spreads to a neighbourhood.** A morphism onto a module of finite
type which is surjective on the stalk at `x` is an epimorphism after pullback to the complement
of the support of its cokernel, an open set containing `x`. -/
private theorem exists_epi_pullback_open_of_stalk_surjective {X : Scheme.{u}}
    {G F : X.Modules} [F.IsFiniteType] (α : G ⟶ F) (x : X)
    (hx : Function.Surjective (stalkLinearMap G F α x)) :
    ∃ V : X.Opens, x ∈ V ∧ Epi ((Scheme.Modules.pullback V.ι).map α) := by
  have hck : (cokernel α).IsFiniteType := Scheme.Modules.isFiniteType_cokernel α inferInstance
  have hx' : x ∉ SheafOfModules.supp (cokernel α) :=
    (Scheme.Modules.surjective_stalkLinearMap_iff_notMem_supp_cokernel α x).mp hx
  let V : X.Opens := ⟨(SheafOfModules.supp (cokernel α))ᶜ,
    (Scheme.Modules.isClosed_supp_cokernel α inferInstance).isOpen_compl⟩
  have hV : IsZero ((Scheme.Modules.pullback V.ι).obj (cokernel α)) :=
    pullback_isZero_of_disjoint_supp_open _ V (Set.disjoint_left.mpr fun _ h hn => h hn)
  exact ⟨V, hx', epi_pullback_map_of_isZero_pullback_cokernel α V hV⟩

/-- A point at which a morphism of modules is an isomorphism on the stalk misses the support of
the kernel: the stalk functor on modules is left exact, so the stalk of the kernel is the kernel
of the stalk map, which vanishes. -/
private theorem notMem_supp_kernel_of_stalk_isIso {Z : Scheme.{u}} {A B : Z.Modules}
    (E : A ⟶ B) (z : Z)
    (h : IsIso ((Scheme.Modules.toPresheaf Z ⋙
      TopCat.Presheaf.stalkFunctor Ab.{u} z).map E)) :
    z ∉ SheafOfModules.supp (kernel E) := by
  have : IsIso ((Scheme.Modules.stalkFunctor Z z).map E) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr
      (ConcreteCategory.bijective_of_isIso ((Scheme.Modules.toPresheaf Z ⋙
        TopCat.Presheaf.stalkFunctor Ab.{u} z).map E))
  exact (Scheme.Modules.notMem_supp_iff_isZero_stalk (kernel E) z).mpr
    ((isZero_kernel_of_mono ((Scheme.Modules.stalkFunctor Z z).map E)).of_iso
      (PreservesKernel.iso (Scheme.Modules.stalkFunctor Z z) E))

/-- The stalk of the pullback of a module along the inclusion of an open set, as a natural
isomorphism of functors, is the stalk of the module itself. -/
private def pullbackOpenStalkIso {X : Scheme.{u}} (V : X.Opens) (x : V) :
    Scheme.Modules.pullback V.ι ⋙ Scheme.Modules.toPresheaf V.toScheme ⋙
      TopCat.Presheaf.stalkFunctor Ab.{u} x ≅
      Scheme.Modules.toPresheaf X ⋙ TopCat.Presheaf.stalkFunctor Ab.{u} x.val :=
  Functor.isoWhiskerRight (Scheme.Modules.restrictFunctorIsoPullback V.ι).symm _ ≪≫
    Scheme.Modules.restrictStalkNatIso V.ι x

/-- A morphism of modules which is an isomorphism after pullback along an open immersion is an
isomorphism after pullback along the inclusion of its image. -/
private theorem isIso_pullback_opensRange_ι {X U : Scheme.{u}} {G F : X.Modules} (α : G ⟶ F)
    (j : U ⟶ X) [IsOpenImmersion j] (hj : IsIso ((Scheme.Modules.pullback j).map α)) :
    IsIso ((Scheme.Modules.pullback j.opensRange.ι).map α) := by
  rw [← j.isoOpensRange_inv_comp]
  exact (Stacks.AlgebraicGeometry.ModuleLimits.isIso_pullback_map_comp_iff
      j.isoOpensRange.inv j (j.isoOpensRange.inv ≫ j) rfl α).mp
    (Functor.map_isIso (Scheme.Modules.pullback j.isoOpensRange.inv)
      ((Scheme.Modules.pullback j).map α))

/-- An isomorphism after pullback to an open `W` of an open `V` is an isomorphism after pullback
to the image of `W` in `X`. -/
private theorem exists_isIso_pullback_open_of_isIso_pullback_pullback {X : Scheme.{u}}
    {G F : X.Modules} (α : G ⟶ F) (V : X.Opens) (W : V.toScheme.Opens) (y : V) (hyW : y ∈ W)
    (hW : IsIso ((Scheme.Modules.pullback W.ι).map ((Scheme.Modules.pullback V.ι).map α))) :
    ∃ W' : X.Opens, y.val ∈ W' ∧ IsIso ((Scheme.Modules.pullback W'.ι).map α) :=
  ⟨(W.ι ≫ V.ι).opensRange, ⟨⟨y, hyW⟩, rfl⟩, isIso_pullback_opensRange_ι α (W.ι ≫ V.ι)
    ((Stacks.AlgebraicGeometry.ModuleLimits.isIso_pullback_map_comp_iff W.ι V.ι _ rfl α).mp hW)⟩

/-- An epimorphism whose kernel is of finite type with support disjoint from an open `W` is an
isomorphism after pullback to `W`. -/
private theorem isIso_pullback_open_of_epi_of_disjoint_supp_kernel {X : Scheme.{u}}
    {A B : X.Modules} (E : A ⟶ B) [Epi E] [(kernel E).IsFiniteType] (W : X.Opens)
    (hW : Disjoint (W : Set X) (SheafOfModules.supp (kernel E))) :
    IsIso ((Scheme.Modules.pullback W.ι).map E) := by
  have : PreservesFiniteLimits (Scheme.Modules.pullback W.ι) :=
    pullback_preservesFiniteLimits_of_isOpenImmersion W.ι
  have hkz : IsZero ((Scheme.Modules.pullback W.ι).obj (kernel E)) :=
    pullback_isZero_of_disjoint_supp_open _ W hW
  have : Mono ((Scheme.Modules.pullback W.ι).map E) :=
    Abelian.mono_of_kernel_ι_eq_zero _
      ((hkz.of_iso (PreservesKernel.iso (Scheme.Modules.pullback W.ι) E).symm).eq_of_src _ _)
  have hcz : IsZero ((Scheme.Modules.pullback W.ι).obj (cokernel E)) :=
    Functor.map_isZero _ (Stacks.AlgebraicGeometry.FiniteTypeSubmodule.isZero_cokernel_of_epi E)
  have := epi_pullback_map_of_isZero_pullback_cokernel E W hcz
  exact isIso_of_mono_of_epi _

/-- **Part (4) of [Stacks, Tag 01Y3] with finite presentation in place of coherence.** A
morphism from a module of finite type to a module of finite presentation which is an isomorphism
on the stalk at `x` is an isomorphism after pullback to an open neighbourhood of `x`. -/
private theorem exists_isIso_pullback_open_of_stalk_isIso {X : Scheme.{u}}
    {G F : X.Modules} [G.IsFiniteType] [F.IsFinitePresentation]
    (α : G ⟶ F) (x : X)
    (hx : IsIso ((Scheme.Modules.toPresheaf X ⋙
      TopCat.Presheaf.stalkFunctor Ab.{u} x).map α)) :
    ∃ V : X.Opens, x ∈ V ∧ IsIso ((Scheme.Modules.pullback V.ι).map α) := by
  have : F.IsFiniteType :=
    (Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isFinitePresentation
      F ‹F.IsFinitePresentation›).2
  have hxbij : Function.Bijective (stalkLinearMap G F α x) :=
    ConcreteCategory.bijective_of_isIso ((Scheme.Modules.toPresheaf X ⋙
      TopCat.Presheaf.stalkFunctor Ab.{u} x).map α)
  obtain ⟨V, hxV, hE⟩ := exists_epi_pullback_open_of_stalk_surjective α x hxbij.2
  let y : V := ⟨x, hxV⟩
  let P := Scheme.Modules.pullback V.ι
  let E := P.map α
  have : Epi E := hE
  have : (P.obj G).IsFiniteType :=
    SheafOfModules.pullback_isFiniteType V.ι.toLRSHom.toShHom G
  have : (P.obj F).IsFinitePresentation :=
    Stacks.Modules.isFinitePresentation_pullback V.ι F ‹F.IsFinitePresentation›
  have : @Epi (SheafOfModules.{u} V.toScheme.ringCatSheaf) (inferInstance) _ _ E :=
    Scheme.Modules.epi_sheafOfModules E
  have hker : (kernel E).IsFiniteType :=
    Stacks.SheafOfModules.LocalKernel.kernel_isFiniteType_of_epi_from_finiteType E
  have hAE : IsIso ((Scheme.Modules.toPresheaf V.toScheme ⋙
      TopCat.Presheaf.stalkFunctor Ab.{u} y).map E) :=
    (NatIso.isIso_map_iff (pullbackOpenStalkIso V y) α).mpr hx
  let W : V.toScheme.Opens := ⟨(SheafOfModules.supp (kernel E))ᶜ,
    (@SheafOfModules.isClosed_supp _ V.toScheme.ringCatSheaf (kernel E) hker).isOpen_compl⟩
  have hyW : y ∈ W := notMem_supp_kernel_of_stalk_isIso E y hAE
  exact exists_isIso_pullback_open_of_isIso_pullback_pullback α V W y hyW
    (isIso_pullback_open_of_epi_of_disjoint_supp_kernel E W
      (Set.disjoint_left.mpr fun _ h hn => h hn))

/-- **An isomorphism on one stalk is an isomorphism on a neighbourhood**, [Stacks, Tag 01Y3]
part (4) in the form the flattening theorem consumes it: the target need only be of finite
presentation over some open `V` containing the point, not globally, and the conclusion is about
pullback along the inclusion of an open rather than restriction to the slice site. -/
theorem exists_isIso_pullback_open_of_stalk_isIso_on_open
    {X : Scheme.{u}} {G F : X.Modules} [G.IsFiniteType]
    (α : G ⟶ F) (V : X.Opens)
    (hfp : ((Scheme.Modules.pullback V.ι).obj F).IsFinitePresentation)
    (x : X) (hxV : x ∈ V)
    (hx : IsIso ((Scheme.Modules.toPresheaf X ⋙
      TopCat.Presheaf.stalkFunctor Ab.{u} x).map α)) :
    ∃ W : X.Opens, x ∈ W ∧ IsIso ((Scheme.Modules.pullback W.ι).map α) := by
  let y : V := ⟨x, hxV⟩
  let P := Scheme.Modules.pullback V.ι
  have : (P.obj G).IsFiniteType :=
    SheafOfModules.pullback_isFiniteType V.ι.toLRSHom.toShHom G
  have : (P.obj F).IsFinitePresentation := hfp
  have hloc : IsIso ((Scheme.Modules.toPresheaf V.toScheme ⋙
      TopCat.Presheaf.stalkFunctor Ab.{u} y).map (P.map α)) :=
    (NatIso.isIso_map_iff (pullbackOpenStalkIso V y) α).mpr hx
  obtain ⟨W, hyW, hW⟩ := exists_isIso_pullback_open_of_stalk_isIso (P.map α) y hloc
  exact exists_isIso_pullback_open_of_isIso_pullback_pullback α V W y hyW hW

end AlgebraicGeometry

end
