module

public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentEtaleChart
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleAffineKernelBaseChange
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentLocality
public import StacksCore.Tactic.StacksAttribute

/-!
# The kernel clause of Stacks 03M1, and the largest quasi-coherent submodule

Let `F` be an algebraic space over a scheme `S` and let `f : M ⟶ N` be a morphism of
quasi-coherent `𝒪_F`-modules.  This file proves that `ker f` is quasi-coherent, with no
hypothesis, and deduces Stacks 04CK: an `𝒪_X`-submodule `G` of a quasi-coherent `𝒪_X`-module
`M` contains a unique quasi-coherent submodule `G'` through which every map from a
quasi-coherent module into `G` factors, and `G'` is the largest quasi-coherent submodule of `M`
contained in `G`.

## Main results

* `Module.BaseChange.bijective_liftBaseChange_of_kernelData`: **flat base change commutes with
  kernels, with both kernels presented by an injection whose image is the kernel of the map of
  sections** rather than by `LinearMap.ker`.
* `SheafOfModules.uliftForPresentationApp`: the map on universe-lifted sections at an object
  induced by a morphism of sheaves of modules.
* `AlgebraicGeometry.Space.SmallEtale.hasSectionBaseChangeOn_kernel`: **the sections of a kernel
  over the objects of a class are the base change of its sections over the chart as soon as those
  of the two modules are**, over a chart whose underlying scheme is affine.
* `AlgebraicGeometry.Space.hasGlobalPresentation_over_kernel`: a kernel of a morphism of
  quasi-coherent `𝒪_F`-modules has a global presentation on every chart with affine underlying
  scheme.
* `AlgebraicGeometry.Space.kernel_isQuasicoherentOnSite` and
  `AlgebraicGeometry.Space.isClosedUnderKernels`: **the kernel clause of Stacks 03M1 for the
  small étale ringed site of an algebraic space, with no hypothesis.**
* `AlgebraicGeometry.Space.existsUnique_largestQuasicoherentSubobject` and
  `AlgebraicGeometry.Space.exists_greatest_quasicoherentSubobject`: **Stacks 04CK**, with no
  hypothesis.

## Implementation notes

The kernel clause is the one closure clause of Stacks 03M1 that global presentations on the
affine charts do not give by themselves: the sections of a kernel over an object of a chart are
the kernel of the sections, and exhibiting *those* as the base change of the sections over the
chart needs the ring map to be flat.  Both inputs of that step are in
`StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleAffineKernelBaseChange` — flatness of the ring
map induced by a morphism between objects with affine underlying scheme, and flat base change of
a kernel; what is carried out here is the assembly they were prepared for.

`Module.BaseChange.bijective_liftBaseChange_of_kernelData` is the algebraic half, and it takes
the two kernels as data: a consumer holds the sections of the kernel sheaf and an injection of
them into the sections of the source, not a `LinearMap.ker`, so asking for that injection
together with the two properties identifying its image keeps the conclusion about the map the
consumer already has.  Inside, the two injections are turned into identifications with the
honest kernels and `Module.BaseChange.bijective_liftBaseChange_ker` is applied across them.

The kernel is the one taken on the whole small étale site, and its restriction `(ker f).over V`
is used as it stands: no comparison with a kernel formed on the slice at the chart is needed.
The three facts identifying the sections of a kernel — vanishing of the composite, injectivity
of the inclusion and exactness on sections — are stated for the restricted morphism `f.over V`,
and each is proved by reading the corresponding fact of
`StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleAffineKernelBaseChange` at the underlying object
`W.left` of the site, the sections of a restriction at `W` being the sections at `W.left` and the
restriction maps agreeing likewise.  They are separate statements because that reading is the one
step of the assembly that unfolds the restriction functor, and doing all three of them inside the
main argument exceeds its elaboration budget.

Two covering families of the chart would be produced by treating `M` and `N` separately, and the
base-change condition for the kernel is needed at one object at a time; the single family
refining both is
`AlgebraicGeometry.Space.SmallEtale.exists_hasSectionBaseChangeOn_pair_of_isQuasicoherentOnSite`.

The module instances of the base-change comparison for `M` and for `N` are rebuilt here with the
same values rather than taken from the hypotheses, because they live inside the statement of
`AlgebraicGeometry.Space.SmallEtale.HasSectionBaseChangeOn` and instance search does not see
them there; the hypotheses are then restated against the rebuilt ones.  The ones for the kernel
need no rebuilding, being the bindings the goal itself introduces.

## References

* [Stacks Project, Tag 03M1](https://stacks.math.columbia.edu/tag/03M1)
* [Stacks Project, Tag 03DN](https://stacks.math.columbia.edu/tag/03DN)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 04CK](https://stacks.math.columbia.edu/tag/04CK)
* [Stacks Project, Tag 0GNB](https://stacks.math.columbia.edu/tag/0GNB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct

namespace Module.BaseChange

/-- An injection onto the kernel of a linear map, with image exactly that kernel, is an
identification with `LinearMap.ker`. -/
private noncomputable def equivKerOfKernelData {R K M N : Type*} [CommRing R]
    [AddCommGroup K] [AddCommGroup M] [AddCommGroup N] [Module R K] [Module R M] [Module R N]
    (g : M →ₗ[R] N) (j : K →ₗ[R] M)
    (hz : ∀ x, g (j x) = 0) (hj : Function.Injective j) (hk : ∀ z, g z = 0 → ∃ x, j x = z) :
    K ≃ₗ[R] LinearMap.ker g :=
  LinearEquiv.ofBijective (j.codRestrict (LinearMap.ker g) fun x => LinearMap.mem_ker.mpr (hz x))
    ⟨fun _ _ hab => hj (congrArg Subtype.val hab),
      fun y => (hk y.1 (LinearMap.mem_ker.mp y.2)).imp fun _ hx => Subtype.ext hx⟩

/-- **Flat base change commutes with kernels, with the two kernels given as data.**

Let `Bc` be a flat `A`-algebra, let `gT` and `gW` be the two maps whose kernels are in question,
and let `jT` and `jW` be injections of two further modules onto those kernels — `hzT`, `hzW`
place the images inside them and `hkT`, `hkW` exhaust them.  If the sources and the targets of
`gT` and `gW` are compared by `rM` and `rN` exhibiting the latter as base changes, and `rK`
compares the two further modules compatibly, then `rK` exhibits its target as the base change of
its source.

The two injections are turned into identifications with `LinearMap.ker gT` and `LinearMap.ker
gW`, and `Module.BaseChange.bijective_liftBaseChange_ker` is transported across them by
`Module.BaseChange.bijective_liftBaseChange_of_comm`. -/
theorem bijective_liftBaseChange_of_kernelData
    {A Bc : Type*} [CommRing A] [CommRing Bc] [Algebra A Bc] [Module.Flat A Bc]
    {MT MW NT NW KT KW : Type*}
    [AddCommGroup MT] [Module A MT]
    [AddCommGroup MW] [Module A MW] [Module Bc MW] [IsScalarTower A Bc MW]
    [AddCommGroup NT] [Module A NT]
    [AddCommGroup NW] [Module A NW] [Module Bc NW] [IsScalarTower A Bc NW]
    [AddCommGroup KT] [Module A KT]
    [AddCommGroup KW] [Module A KW] [Module Bc KW] [IsScalarTower A Bc KW]
    {rM : MT →ₗ[A] MW} {rN : NT →ₗ[A] NW} {rK : KT →ₗ[A] KW}
    (hM : Function.Bijective (rM.liftBaseChange Bc))
    (hN : Function.Bijective (rN.liftBaseChange Bc))
    (gT : MT →ₗ[A] NT) (gW : MW →ₗ[Bc] NW)
    (jT : KT →ₗ[A] MT) (jW : KW →ₗ[Bc] MW)
    (hzT : ∀ x, gT (jT x) = 0) (hzW : ∀ y, gW (jW y) = 0)
    (hjT : Function.Injective jT) (hjW : Function.Injective jW)
    (hkT : ∀ z, gT z = 0 → ∃ x, jT x = z) (hkW : ∀ z, gW z = 0 → ∃ y, jW y = z)
    (hng : ∀ x, rN (gT x) = gW (rM x)) (hnj : ∀ x, jW (rK x) = rM (jT x)) :
    Function.Bijective (rK.liftBaseChange Bc) := by
  have hmem : ∀ x : LinearMap.ker gT, rM (x : MT) ∈ LinearMap.ker gW := fun x => by
    rw [LinearMap.mem_ker, ← hng, LinearMap.mem_ker.mp x.2, map_zero]
  let kap : LinearMap.ker gT →ₗ[A] LinearMap.ker gW :=
    { toFun := fun x => ⟨rM (x : MT), hmem x⟩
      map_add' := fun x y => Subtype.ext (map_add rM (x : MT) (y : MT))
      map_smul' := fun c x => Subtype.ext (map_smul rM c (x : MT)) }
  have hbij := bijective_liftBaseChange_ker A Bc gT gW rM rN hng hM hN kap fun _ => rfl
  refine bijective_liftBaseChange_of_comm rK kap
    (equivKerOfKernelData gT jT hzT hjT hkT) (equivKerOfKernelData gW jW hzW hjW hkW)
    (fun n => Subtype.ext (hnj n)) hbij

end Module.BaseChange

namespace SheafOfModules

universe w v r m t

variable {C : Type w} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{r}}

/-- The map on the universe-lifted sections at an object induced by a morphism of sheaves of
modules.  The universe lift of `SheafOfModules.uliftForPresentation` acts on the sections by
`ULift.up`, so the induced map is the component of the morphism read through it. -/
def uliftForPresentationApp {M N : SheafOfModules.{m} R} (φ : M ⟶ N) (U : Cᵒᵖ) :
    (uliftForPresentation.{w, v, r, m, t} M).val.obj U →ₗ[R.obj.obj U]
      (uliftForPresentation.{w, v, r, m, t} N).val.obj U where
  toFun x := ULift.up (φ.val.app U x.down)
  map_add' x y := congrArg ULift.up (map_add (φ.val.app U).hom x.down y.down)
  map_smul' c x := congrArg ULift.up (map_smul (φ.val.app U).hom c x.down)

/-- The map on universe-lifted sections induced by a morphism of sheaves of modules commutes with
restriction, by naturality of the morphism. -/
theorem uliftForPresentationApp_map_apply {M N : SheafOfModules.{m} R} (φ : M ⟶ N) {U U' : Cᵒᵖ}
    (h : U ⟶ U') (x : (uliftForPresentation.{w, v, r, m, t} M).val.obj U) :
    (uliftForPresentation.{w, v, r, m, t} N).val.map h (uliftForPresentationApp φ U x) =
      uliftForPresentationApp φ U' ((uliftForPresentation.{w, v, r, m, t} M).val.map h x) :=
  congrArg ULift.up (PresheafOfModules.naturality_apply φ.val h x.down).symm

end SheafOfModules

universe m u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

namespace SmallEtale

/-- The composite of the inclusion of a kernel of `𝒪_F`-modules with the morphism vanishes on
the universe-lifted sections over an object of the slice at a chart. -/
theorem uliftApp_over_kernel_eq_zero {M N : Modules.{u, max (u + 1) m} B S hS F hF} (f : M ⟶ N)
    (V : (smallEtaleRingedSite B S hS F hF).C) (W : (Over V)ᵒᵖ)
    (x : (SheafOfModules.uliftForPresentation.{u + 1, u, u, max (u + 1) m, u + 1}
      ((kernel f).over V)).val.obj W) :
    SheafOfModules.uliftForPresentationApp (f.over V) W
      (SheafOfModules.uliftForPresentationApp ((kernel.ι f).over V) W x) = 0 :=
  congrArg ULift.up (app_kernel_ι_comp_eq_zero B S hS F hF f (op W.unop.left) x.down)

/-- The inclusion of a kernel of `𝒪_F`-modules is injective on the universe-lifted sections over
an object of the slice at a chart. -/
theorem uliftApp_over_kernel_injective {M N : Modules.{u, max (u + 1) m} B S hS F hF} (f : M ⟶ N)
    (V : (smallEtaleRingedSite B S hS F hF).C) (W : (Over V)ᵒᵖ) :
    Function.Injective (fun x : (SheafOfModules.uliftForPresentation.{u + 1, u, u,
        max (u + 1) m, u + 1} ((kernel f).over V)).val.obj W =>
      SheafOfModules.uliftForPresentationApp ((kernel.ι f).over V) W x) := fun _ _ hab =>
  ULift.down_injective
    (injective_app_kernel_ι B S hS F hF f (op W.unop.left) (congrArg ULift.down hab))

/-- A universe-lifted section of the source of a morphism of `𝒪_F`-modules killed by it over an
object of the slice at a chart is the image of a section of the kernel. -/
theorem uliftApp_over_exists_kernel {M N : Modules.{u, max (u + 1) m} B S hS F hF} (f : M ⟶ N)
    (V : (smallEtaleRingedSite B S hS F hF).C) (W : (Over V)ᵒᵖ)
    (z : (SheafOfModules.uliftForPresentation.{u + 1, u, u, max (u + 1) m, u + 1}
      (M.over V)).val.obj W)
    (hz : SheafOfModules.uliftForPresentationApp (f.over V) W z = 0) :
    ∃ x, SheafOfModules.uliftForPresentationApp ((kernel.ι f).over V) W x = z := by
  obtain ⟨w, hw⟩ := exists_app_kernel_ι_eq B S hS F hF f (op W.unop.left) z.down
    (congrArg ULift.down hz)
  exact ⟨ULift.up w, ULift.down_injective hw⟩

/-- **The sections of a kernel over the objects of a class are the base change of its sections
over the chart as soon as those of the two modules are.**  Let `V` be a chart with affine
underlying scheme and let `f : M ⟶ N` be a morphism of `𝒪_F`-modules; if the base-change
condition holds for `M` and for `N` at every object of a class `Q` consisting of objects with
affine underlying scheme, then it holds for `ker f` there.

The ring map induced on global functions by the structural morphism of such an object is flat,
every morphism of the small étale site being étale
(`AlgebraicGeometry.Space.SmallEtale.flat_gamma_of_isAffine`), and the sections of the kernel are
the kernel of the sections, so this is
`Module.BaseChange.bijective_liftBaseChange_of_kernelData`. -/
theorem hasSectionBaseChangeOn_kernel {V : (smallEtaleRingedSite B S hS F hF).C}
    (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj V)))
    {M N : Modules.{u, max (u + 1) m} B S hS F hF} (f : M ⟶ N) {Q : Over V → Prop}
    (hQ : ∀ W : Over V, Q W → IsAffine ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS F).obj W.left)))
    (hM : HasSectionBaseChangeOn B S hS F hF
      (SheafOfModules.uliftForPresentation.{u + 1, u, u, max (u + 1) m, u + 1} (M.over V)) Q)
    (hN : HasSectionBaseChangeOn B S hS F hF
      (SheafOfModules.uliftForPresentation.{u + 1, u, u, max (u + 1) m, u + 1} (N.over V)) Q) :
    HasSectionBaseChangeOn B S hS F hF
      (SheafOfModules.uliftForPresentation.{u + 1, u, u, max (u + 1) m, u + 1}
        ((kernel f).over V)) Q := by
  intro W hQW mKT mKW algW mKWA twKW
  have hflat := SmallEtale.flat_gamma_of_isAffine B S hS F (U := W.left) (W := V)
    (Over.mkIdTerminal.from W : W ⟶ Over.mk (𝟙 V)).left (hQ W hQW) hV rfl
  let mUT : ∀ X : SheafOfModules.{max (u + 1) m}
      (((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)).over V),
      Module Γ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj V), ⊤)
        (X.val.obj (op (Over.mk (𝟙 V)))) := fun X =>
    inferInstanceAs (Module
      ((((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS F hF).O)).over V).obj.obj
        (op (Over.mk (𝟙 V)))) (X.val.obj (op (Over.mk (𝟙 V)))))
  let mUW : ∀ X : SheafOfModules.{max (u + 1) m}
      (((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)).over V),
      Module Γ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj W.left), ⊤)
        (X.val.obj (op W)) := fun X =>
    inferInstanceAs (Module
      ((((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS F hF).O)).over V).obj.obj (op W))
      (X.val.obj (op W)))
  let mUWA : ∀ X : SheafOfModules.{max (u + 1) m}
      (((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)).over V),
      Module Γ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj V), ⊤)
        (X.val.obj (op W)) := fun X =>
    Module.compHom _ (algebraMap
      Γ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj V), ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj W.left), ⊤))
  have twUW : ∀ X : SheafOfModules.{max (u + 1) m}
      (((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)).over V),
      IsScalarTower
        Γ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj V), ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj W.left), ⊤)
        (X.val.obj (op W)) := fun _ =>
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let res : ∀ X : SheafOfModules.{max (u + 1) m}
      (((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)).over V),
      X.val.obj (op (Over.mk (𝟙 V))) →ₗ[Γ((BigFppfOver.toScheme B S hS).obj
        ((SmallEtale.toOver B S hS F).obj V), ⊤)] X.val.obj (op W) := fun X =>
    { toFun := fun n => X.val.map (Over.mkIdTerminal.from W).op n
      map_add' := map_add (X.val.map (Over.mkIdTerminal.from W).op).hom
      map_smul' := fun c n =>
        (X.val.map_smul (Over.mkIdTerminal.from W).op c n).symm ▸ rfl }
  have hM' : Function.Bijective ((res (SheafOfModules.uliftForPresentation.{u + 1, u, u,
      max (u + 1) m, u + 1} (M.over V))).liftBaseChange
      Γ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj W.left), ⊤)) :=
    hM W hQW
  have hN' : Function.Bijective ((res (SheafOfModules.uliftForPresentation.{u + 1, u, u,
      max (u + 1) m, u + 1} (N.over V))).liftBaseChange
      Γ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj W.left), ⊤)) :=
    hN W hQW
  exact Module.BaseChange.bijective_liftBaseChange_of_kernelData hM' hN'
    (SheafOfModules.uliftForPresentationApp (f.over V) (op (Over.mk (𝟙 V))))
    (SheafOfModules.uliftForPresentationApp (f.over V) (op W))
    (SheafOfModules.uliftForPresentationApp ((kernel.ι f).over V) (op (Over.mk (𝟙 V))))
    (SheafOfModules.uliftForPresentationApp ((kernel.ι f).over V) (op W))
    (uliftApp_over_kernel_eq_zero B S hS F hF f V (op (Over.mk (𝟙 V))))
    (uliftApp_over_kernel_eq_zero B S hS F hF f V (op W))
    (uliftApp_over_kernel_injective B S hS F hF f V (op (Over.mk (𝟙 V))))
    (uliftApp_over_kernel_injective B S hS F hF f V (op W))
    (uliftApp_over_exists_kernel B S hS F hF f V (op (Over.mk (𝟙 V))))
    (uliftApp_over_exists_kernel B S hS F hF f V (op W))
    (fun x => SheafOfModules.uliftForPresentationApp_map_apply (f.over V)
      (Over.mkIdTerminal.from W : W ⟶ Over.mk (𝟙 V)).op x)
    (fun x => (SheafOfModules.uliftForPresentationApp_map_apply ((kernel.ι f).over V)
      (Over.mkIdTerminal.from W : W ⟶ Over.mk (𝟙 V)).op x).symm)

end SmallEtale

/-- **A kernel of a morphism of quasi-coherent `𝒪_F`-modules has a global presentation on every
chart whose underlying scheme is affine.**

The base-change condition for the two modules holds over one common covering family of the chart
(`AlgebraicGeometry.Space.SmallEtale`'s
`exists_hasSectionBaseChangeOn_pair_of_isQuasicoherentOnSite`), hence for the kernel by
`AlgebraicGeometry.Space.SmallEtale.hasSectionBaseChangeOn_kernel`, and a module whose sections
are base changes over such a family is globally presented. -/
theorem hasGlobalPresentation_over_kernel {M N : Modules.{u, max (u + 1) m} B S hS F hF}
    (f : M ⟶ N) (hM : M.IsQuasicoherentOnSite) (hN : N.IsQuasicoherentOnSite)
    (V : (smallEtaleRingedSite B S hS F hF).C)
    (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj V))) :
    ((kernel f).over V).HasGlobalPresentation := by
  obtain ⟨k, Z, gZ, hcov, hZaff, hbcM, hbcN⟩ :=
    SmallEtale.exists_hasSectionBaseChangeOn_pair_of_isQuasicoherentOnSite B S hS F hF M N
      hM hN V hV
  exact SmallEtale.hasGlobalPresentation_of_hasSectionBaseChangeOn B S hS F hF
    ((kernel f).over V) hV gZ hcov
    (SmallEtale.hasSectionBaseChangeOn_kernel B S hS F hF hV f (fun _ hW => hW.1) hbcM hbcN)

/-- **The kernel clause of Stacks 03M1 for the small étale ringed site of an algebraic space**,
with no hypothesis: a kernel of a morphism of quasi-coherent `𝒪_F`-modules is quasi-coherent.

The étale charts with affine underlying scheme cover the final object of the small étale site,
the kernel is globally presented on each of them by
`AlgebraicGeometry.Space.hasGlobalPresentation_over_kernel`, and a module globally presented on a
covering family of the final object is quasi-coherent. -/
theorem kernel_isQuasicoherentOnSite {M N : Modules.{u, max (u + 1) m} B S hS F hF} (f : M ⟶ N)
    (hM : M.IsQuasicoherentOnSite) (hN : N.IsQuasicoherentOnSite) :
    (kernel f).IsQuasicoherentOnSite :=
  Stacks.SheafOfModules.isQuasicoherentOnSite_of_coversTop_hasGlobalPresentation (kernel f)
    (SmallEtale.coversTop_affineCharts B S hS F)
    fun V => hasGlobalPresentation_over_kernel B S hS F hF f hM hN V.1 V.2

/-- **The kernel clause of Stacks 03M1 for the small étale ringed site of an algebraic space**, in
the form of the `CategoryTheory.ObjectProperty.IsClosedUnderKernels` class, with no hypothesis.

It is the instance hypothesis of
`AlgebraicGeometry.Space.existsUnique_quasicoherentSubobject_of_isClosedUnderKernels`.  The class
asks about the vertex of an arbitrary limiting kernel fork, so the canonical kernel is
transported along `CategoryTheory.Limits.IsLimit.conePointUniqueUpToIso`. -/
theorem isClosedUnderKernels :
    ObjectProperty.IsClosedUnderKernels
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, max (u + 1) m}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))) where
  kernels_le := by
    rintro _ ⟨f, k, hk, hf⟩
    exact ObjectProperty.prop_of_iso _ (IsLimit.conePointUniqueUpToIso (kernelIsKernel f) hk)
      (kernel_isQuasicoherentOnSite B S hS F hF f hf.1 hf.2)

/-- **Stacks 04CK.**  Let `S` be a scheme, let `X` be an algebraic space over `S`, let `𝓕` be a
quasi-coherent `𝒪_X`-module and let `𝒢 ⊆ 𝓕` be an `𝒪_X`-submodule.  There is a unique
quasi-coherent `𝒪_X`-submodule `𝒢' ⊆ 𝒢` for which composition with the inclusion `𝒢' ⊆ 𝒢` is a
bijection `Hom(𝓗, 𝒢') ⟶ Hom(𝓗, 𝒢)` for every quasi-coherent `𝒪_X`-module `𝓗`.

This is `AlgebraicGeometry.Space.existsUnique_quasicoherentSubobject_of_isClosedUnderKernels`
with its kernel hypothesis discharged by
`AlgebraicGeometry.Space.isClosedUnderKernels`. -/
@[stacks 04CK]
theorem existsUnique_largestQuasicoherentSubobject (M : Modules.{u, m} B S hS F hF)
    [M.IsQuasicoherentOnSite] (G : Subobject M) :
    ∃! G' : { G' : Subobject (G : Modules.{u, m} B S hS F hF) //
        (G' : Modules.{u, m} B S hS F hF).IsQuasicoherentOnSite },
      ∀ (H : Modules.{u, m} B S hS F hF) [H.IsQuasicoherentOnSite],
        Function.Bijective
          (fun f : H ⟶ (G'.1 : Modules.{u, m} B S hS F hF) ↦ f ≫ G'.1.arrow) :=
  have _ := isClosedUnderKernels B S hS F hF
  existsUnique_quasicoherentSubobject_of_isClosedUnderKernels B S hS F hF M G

/-- **Stacks 04CK, the maximality clause.**  The quasi-coherent submodule of
`AlgebraicGeometry.Space.existsUnique_largestQuasicoherentSubobject` is the largest
quasi-coherent submodule of `𝓕` contained in `𝒢`.

This is `AlgebraicGeometry.Space.exists_greatest_quasicoherentSubobject_of_isClosedUnderKernels`
with its kernel hypothesis discharged by
`AlgebraicGeometry.Space.isClosedUnderKernels`. -/
@[stacks 04CK]
theorem exists_greatest_quasicoherentSubobject (M : Modules.{u, m} B S hS F hF)
    [M.IsQuasicoherentOnSite] (G : Subobject M) :
    ∃ G' : Subobject (G : Modules.{u, m} B S hS F hF),
      (G' : Modules.{u, m} B S hS F hF).IsQuasicoherentOnSite ∧
        ∀ K : Subobject (G : Modules.{u, m} B S hS F hF),
          (K : Modules.{u, m} B S hS F hF).IsQuasicoherentOnSite → K ≤ G' :=
  have _ := isClosedUnderKernels B S hS F hF
  exists_greatest_quasicoherentSubobject_of_isClosedUnderKernels B S hS F hF M G

end AlgebraicGeometry.Space

end
