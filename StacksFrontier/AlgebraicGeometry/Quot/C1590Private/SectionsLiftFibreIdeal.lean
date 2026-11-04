module

public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.SectionsLiftCohomology
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperGlobalSections.FibreThickening
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionKerIdealFibre
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionModuleEssentialImage
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionModulePushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.GlobalSectionsRightExact
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePushforwardBaseScalars
public import StacksFrontier.AlgebraicGeometry.Spaces.StrictTransformLocalGenerators

/-!
# The fibre of an algebraic space over a closed point of an affine base

Let `f : X ⟶ V` be a morphism from an algebraic space to an affine scheme `V` of the site, with
`A = Γ(V, 𝒪_V)`, let `p : T ⟶ V` be a closed immersion of schemes with ideal `𝔪 ⊆ A`, and let
`q : W ⟶ X` present the fibre `X ×_V T`.  Then `q` is a closed immersion, and an `𝒪_X`-module
`G` is annihilated by the ideal sheaf `𝓘 = ker(q♯)` cutting out the fibre as soon as
multiplication by every `a ∈ 𝔪` vanishes on it.  Conversely every direct image along `q` is
killed by `𝔪`.

## Main results

* `AlgebraicGeometry.C1590Private.isClosedImmersion_fibre`: `q` is a closed immersion.
* `AlgebraicGeometry.C1590Private.isKilledBy_modulePushforward_fibre`: `𝔪` kills `q_* N`.
* `AlgebraicGeometry.C1590Private.annihilatedByKerIdeal_of_isKilledBy`: a module killed by `𝔪`
  is annihilated by the ideal of the fibre.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.SiteModules

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

universe u

namespace AlgebraicGeometry.C1590Private

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (Vb : BigFppfOver B S hS) {X : AlgebraicSpaces B S hS} (f : X ⟶ schemeSpace Vb)
  {T W : BigFppfOver B S hS} (p : T ⟶ Vb) (v : W ⟶ T) (q : yoneda.obj W ⟶ X.1)
  (hpb : IsPullback q (yoneda.map v) f.hom (yoneda.map p))

/-- The ideal `𝔪 = ker (Γ(V) ⟶ Γ(T))` of a morphism of schemes `p : T ⟶ V`. -/
abbrev fibreIdeal : Ideal Γ((BigFppfOver.toScheme B S hS).obj Vb, ⊤) :=
  RingHom.ker ((BigFppfOver.toScheme B S hS).map p).appTop.hom

/-- The presentation `q : W ⟶ X` of the fibre, as a morphism of algebraic spaces. -/
abbrev fibrePresentationMap : schemeSpace W ⟶ X := ObjectProperty.homMk q

include hpb in
/-- If `p` is a closed immersion, so is the presentation `q` of the fibre `X ×_V T`. -/
theorem isClosedImmersion_fibre
    (hp : AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map p)) :
    Space.IsClosedImmersion B S hS q :=
  (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback hpb.flip
    ((BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS
      (@AlgebraicGeometry.IsClosedImmersion.{u}) p).2 hp)

include hpb in
/-- The ideal `𝔪` kills the direct image along `q` of every module on the fibre. -/
theorem isKilledBy_modulePushforward_fibre
    (N : Space.Modules.{u, u} B S hS (schemeSpace W).1 (schemeSpace W).2) :
    IsKilledBy (Space.pullbackRingHom B Vb f) (fibreIdeal Vb p)
      ((Space.modulePushforward B S hS (fibrePresentationMap q)).obj N) := by
  intro a ha
  have h1 := Space.modulePushforward_map_globalSmul_pullbackToGlobalFunctions B S hS
    (fibrePresentationMap q) f N a
  have h2 : fibrePresentationMap q ≫ f = schemeSpaceMap v ≫ schemeSpaceMap p :=
    ObjectProperty.hom_ext _ hpb.w
  have h3 : Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map p).op a = 0 := ha
  have h4 : Space.pullbackToGlobalFunctions B S hS (schemeSpace W) T (schemeSpaceMap v)
      (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map p).op a) =
        (0 : ↥(GlobalSectionRing (Stacks.SheafOfModules.Tensor.ringSheaf
          (Space.smallEtaleRingedSite B S hS (schemeSpace W).1 (schemeSpace W).2).O))) := by
    rw [h3]; exact map_zero _
  rw [h2, Space.pullbackToGlobalFunctions_comp_schemeSpaceMap, h4, globalSmul_zero,
    Functor.map_zero] at h1
  exact h1.symm

section FibreThickening

variable [IsAffine ((BigFppfOver.toScheme B S hS).obj Vb)]

/-- The ideal sheaf of `p` lies in that of `Spec (A / 𝔪) ⟶ V`. -/
theorem fibreIdeal_ker_le
    (_hp : AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map p)) :
    ((BigFppfOver.toScheme B S hS).map p).ker ≤
      ((BigFppfOver.toScheme B S hS).map
        (Space.adicCompletionQuotientObjHom B S hS Vb (fibreIdeal Vb p) 1)).ker := by
  rw [Scheme.ker_of_isAffine, Scheme.ker_of_isAffine,
    Space.ker_appTop_adicCompletionQuotientObjHom, pow_one]

/-- The morphism of schemes `Spec (A / 𝔪) ⟶ T` through which `Spec (A / 𝔪) ⟶ V` factors. -/
def adicQuotientToFibreBaseScheme
    (hp : AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map p)) :
    (BigFppfOver.toScheme B S hS).obj
      (Space.adicCompletionQuotientObj B S hS Vb (fibreIdeal Vb p) 1) ⟶
      (BigFppfOver.toScheme B S hS).obj T :=
  IsClosedImmersion.lift ((BigFppfOver.toScheme B S hS).map p)
    ((BigFppfOver.toScheme B S hS).map
      (Space.adicCompletionQuotientObjHom B S hS Vb (fibreIdeal Vb p) 1))
    (fibreIdeal_ker_le Vb p hp)

/-- The factorization of `Spec (A / 𝔪) ⟶ V` through `p`, on schemes. -/
theorem adicQuotientToFibreBaseScheme_comp
    (hp : AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map p)) :
    adicQuotientToFibreBaseScheme Vb p hp ≫ (BigFppfOver.toScheme B S hS).map p =
      (BigFppfOver.toScheme B S hS).map
        (Space.adicCompletionQuotientObjHom B S hS Vb (fibreIdeal Vb p) 1) :=
  IsClosedImmersion.lift_fac _ _ _

/-- The morphism `Spec (A / 𝔪) ⟶ T` of the site through which `Spec (A / 𝔪) ⟶ V` factors. -/
def adicQuotientToFibreBase
    (hp : AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map p)) :
    Space.adicCompletionQuotientObj B S hS Vb (fibreIdeal Vb p) 1 ⟶ T :=
  Over.homMk (ObjectProperty.homMk (adicQuotientToFibreBaseScheme Vb p hp)) (by
    apply ObjectProperty.hom_ext
    have h2 : (BigFppfOver.toScheme B S hS).map p ≫ Vb.hom.hom = T.hom.hom :=
      congrArg (fun k => k.hom) (Over.w p)
    have h3 : (BigFppfOver.toScheme B S hS).map
        (Space.adicCompletionQuotientObjHom B S hS Vb (fibreIdeal Vb p) 1) ≫ Vb.hom.hom =
        (Space.adicCompletionQuotientObj B S hS Vb (fibreIdeal Vb p) 1).hom.hom :=
      congrArg (fun k => k.hom)
        (Over.w (Space.adicCompletionQuotientObjHom B S hS Vb (fibreIdeal Vb p) 1))
    change adicQuotientToFibreBaseScheme Vb p hp ≫ T.hom.hom = _
    rw [← h2, ← Category.assoc, adicQuotientToFibreBaseScheme_comp, h3])

/-- The factorization of `Spec (A / 𝔪) ⟶ V` through `p`, in the site. -/
theorem adicQuotientToFibreBase_comp
    (hp : AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map p)) :
    adicQuotientToFibreBase Vb p hp ≫ p =
      Space.adicCompletionQuotientObjHom B S hS Vb (fibreIdeal Vb p) 1 :=
  (BigFppfOver.toScheme B S hS).map_injective (by
    rw [Functor.map_comp]
    exact adicQuotientToFibreBaseScheme_comp Vb p hp)

/-- The closed subspace `X ×_V Spec (A / 𝔪)` of `X`. -/
abbrev fibreSubspace : Space.ClosedSubspaces B S hS X.1 :=
  Space.fibreThickening Vb (fibreIdeal Vb p) f 1

include hpb in
/-- The inclusion of `X ×_V Spec (A / 𝔪)` into `X` factors through `q`. -/
theorem exists_fibreSubspace_ι_eq
    (hp : AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map p)) :
    ∃ h : (fibreSubspace Vb f p).1.toFunctor ⟶ yoneda.obj W,
      h ≫ q = (fibreSubspace Vb f p).1.ι := by
  let j := Space.adicCompletionQuotientObjHom B S hS Vb (fibreIdeal Vb p) 1
  have : Mono j := (BigFppfOver.toScheme B S hS).mono_of_mono_map inferInstance
  let R := Subfunctor.range (yoneda.map j)
  let fh : X.1 ⟶ yoneda.obj Vb := f.hom
  let k : (fibreSubspace Vb f p).1.toFunctor ⟶ yoneda.obj T :=
    R.fromPreimage fh ≫ inv (Subfunctor.toRange (yoneda.map j)) ≫
      yoneda.map (adicQuotientToFibreBase Vb p hp)
  have hr : inv (Subfunctor.toRange (yoneda.map j)) ≫ yoneda.map j = R.ι := by
    rw [IsIso.inv_comp_eq, Subfunctor.toRange_ι]
  have hk : (fibreSubspace Vb f p).1.ι ≫ f.hom = k ≫ yoneda.map p := by
    show _ = (R.fromPreimage fh ≫ inv (Subfunctor.toRange (yoneda.map j)) ≫
      yoneda.map (adicQuotientToFibreBase Vb p hp)) ≫ yoneda.map p
    rw [Category.assoc, Category.assoc, ← Functor.map_comp, adicQuotientToFibreBase_comp, hr,
      Subfunctor.fromPreimage_ι]
    rfl
  exact ⟨hpb.lift _ _ hk, hpb.lift_fst _ _ hk⟩

include hpb in
/-- A function on an étale chart of `X` vanishing on the fibre lies in the kernel of
`𝒪_X ⟶ 𝒪_X / 𝔪 𝒪_X`. -/
theorem mem_idealKernel_of_mem_kerIdeal
    (hp : AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map p))
    (U : Space.SmallEtale B S hS X.1)
    (s : ToType ((Space.structureRingSheaf B S hS X).obj.obj (op U)))
    (hs : s ∈ (SheafOfModules.kerIdeal
      (Space.structureSharp B S hS (fibrePresentationMap q))).obj (op U)) :
    s ∈ (Space.idealKernel (Space.pullbackRingHom B Vb f) (fibreIdeal Vb p ^ 1)).obj (op U) := by
  have hq := isClosedImmersion_fibre Vb f p v q hpb hp
  obtain ⟨h, hh⟩ := exists_fibreSubspace_ι_eq Vb f p v q hpb hp
  have hZ := (fibreSubspace Vb f p).2.2.rep
  rw [Space.mem_kerIdeal_structureSharp_iff B S hS (fibrePresentationMap q) hq.rep U] at hs
  rw [← Space.definingIdealSheaf_fibreThickening]
  show s ∈ Space.definingIdealAt B S hS X (fibreSubspace Vb f p) (op U)
  rw [Space.definingIdealAt_eq_ker]
  have hw : (hZ.fst U.1.hom ≫ h) ≫ q = yoneda.map (hZ.snd U.1.hom) ≫ U.1.hom := by
    rw [Category.assoc, hh]
    exact hZ.w U.1.hom
  have hws : hq.rep.lift (hZ.fst U.1.hom ≫ h) (hZ.snd U.1.hom) hw ≫ hq.rep.snd U.1.hom =
      hZ.snd U.1.hom := hq.rep.lift_snd _ _ hw
  show (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map (hZ.snd U.1.hom)).op).hom s = 0
  rw [← hws, Functor.map_comp, op_comp, Functor.map_comp, CommRingCat.hom_comp]
  exact (congrArg (fun z => (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map
    (hq.rep.lift (hZ.fst U.1.hom ≫ h) (hZ.snd U.1.hom) hw)).op).hom z) hs).trans (map_zero _)

include hpb in
/-- An `𝒪_X`-module killed by `𝔪` is annihilated by the ideal sheaf of the fibre. -/
theorem annihilatedByKerIdeal_of_isKilledBy
    (hp : AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map p))
    (G : Space.Modules.{u, u} B S hS X.1 X.2)
    (hG : IsKilledBy (Space.pullbackRingHom B Vb f) (fibreIdeal Vb p) G) :
    Space.AnnihilatedByKerIdeal B S hS (fibrePresentationMap q) G := by
  intro U a ha m
  refine Stacks.eq_of_isSeparated G (Space.generate_isAffine_mem_topology B S hS X.1 U.unop)
    fun W g hg => ?_
  obtain ⟨Z, h, k', hk', rfl⟩ := hg
  let : Module ((Space.structureRingSheaf B S hS X).obj.obj (op Z)) (G.val.obj (op Z)) :=
    (G.val.obj (op Z)).isModule
  have key : ∀ x ∈ Ideal.map (Space.idealChartEval (Space.pullbackRingHom B Vb f) Z)
      (fibreIdeal Vb p), ∀ n : G.val.obj (op Z), x • n = 0 := by
    intro x hx
    refine Submodule.span_induction (p := fun x _ => ∀ n : G.val.obj (op Z), x • n = 0)
      ?_ ?_ ?_ ?_ hx
    · rintro _ ⟨b, hb, rfl⟩ n
      exact congrArg (fun g => g.val.app (op Z) n) (hG b hb)
    · exact fun n => zero_smul _ _
    · intro x y _ _ hx hy n
      rw [add_smul, hx, hy, add_zero]
    · intro c x _ hx n
      rw [smul_eq_mul, mul_smul, hx, smul_zero]
  have ha' := (SheafOfModules.kerIdeal
    (Space.structureSharp B S hS (fibrePresentationMap q))).map_mem k'.op ha
  have hI := (Space.mem_idealKernel_iff_of_isAffine (Space.pullbackRingHom B Vb f)
    (fibreIdeal Vb p ^ 1) Z hk' _).1 (mem_idealKernel_of_mem_kerIdeal Vb f p v q hpb hp Z _ ha')
  rw [pow_one] at hI
  refine (PresheafOfModules.map_comp_apply G.val k'.op h.op _).trans ?_
  refine Eq.trans ?_ (map_zero (ConcreteCategory.hom (G.val.map (h ≫ k').op))).symm
  refine (congrArg (G.val.map h.op) ((PresheafOfModules.map_smul G.val k'.op a m).trans ?_)).trans
    (map_zero _)
  exact key _ hI _

end FibreThickening

end AlgebraicGeometry.C1590Private

end
