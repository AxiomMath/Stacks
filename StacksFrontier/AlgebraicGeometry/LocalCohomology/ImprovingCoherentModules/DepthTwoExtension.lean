module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.Regular.RegularSequence
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Mono
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Support
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.SupportClosure
public import StacksFrontier.AlgebraicGeometry.Divisors.HartogsExtension.Basic
public import StacksFrontier.AlgebraicGeometry.CoherentTFAE.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.FiniteType
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FiniteTypeExtension
public import StacksFrontier.RingTheory.Depth.AssociatedPrime
public import StacksFrontier.RingTheory.Depth.Defs.Defs
public import StacksFrontier.RingTheory.Ideal.AssociatedPrime.Defs
public import StacksFrontier.Topology.Sheaves.Modules.Colimits
public import StacksFrontier.Topology.Sheaves.Modules.Exactness
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CoherentFinitePresentation
public import StacksCore.Tactic.StacksAttribute

/-!
# Uniqueness of the depth-two extension along a subset

A map of modules on a scheme is a *depth-two extension along `T`* when its target is coherent,
it is an isomorphism on stalks away from `T`, and the stalks of its target have depth at least
two at every point of `T`.  Two depth-two extensions of one module along the same subset are
isomorphic by a unique isomorphism over that module.

## Main definitions

* `AlgebraicGeometry.IsDepthTwoExtension` records coherence of the target, agreement off the
  subset, and depth at least two on it.

## Main results

* `AlgebraicGeometry.depthTwoExtension_unique`: two depth-two extensions of the same module
  along the same subset are uniquely isomorphic under it.

## Implementation notes

The subset `T` is arbitrary — neither closed nor stable under specialization — and the common
source is an arbitrary module, not a coherent one.  Both of those are used in the construction
of the comparison isomorphism, so the proof cannot simply restrict to the complement of `T`:

* The common source is divided by the kernel of one of the two maps.  That kernel is killed by
  the other map, because a map to a coherent module vanishes once its stalk map vanishes at
  every associated point of the target, and depth at least one at a point of `T` says exactly
  that the point is not associated.  So both maps factor through one coimage `Q`, by maps `a`
  and `b` which are monomorphisms and are isomorphisms on stalks away from `T`.
* The open set on which the comparison is built is the complement of the supports of the two
  cokernels.  Those supports are closed because a quotient of a module of finite type is of
  finite type, and they lie in `T` because a stalkwise isomorphism has vanishing cokernel
  stalk.  On that open set `a` and `b` are isomorphisms on all stalks, hence isomorphisms, and
  the Hartogs-type isomorphism [Stacks, Tag 0E9I] identifies each target with the pushforward
  of its restriction there.

Uniqueness needs no further rigidity: the restriction of the first map to that open set is an
epimorphism, and the Hartogs isomorphism makes restriction injective on morphisms out of the
target.

## References

* [Stacks Project, Tag 0EI3](https://stacks.math.columbia.edu/tag/0EI3)
* [Stacks Project, Tag 0E9I](https://stacks.math.columbia.edu/tag/0E9I)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry

variable {X : Scheme.{u}}

/-! ### Stalks of sheaves of modules on a scheme -/

/-- The stalk at `x` of the underlying abelian presheaf of a sheaf of `𝒪_X`-modules, as a
functor. -/
private noncomputable abbrev stalkAb (X : Scheme.{u}) (x : X) :
    SheafOfModules.{u} X.ringCatSheaf ⥤ AddCommGrpCat.{u} :=
  SheafOfModules.stalkAddCommGroupFunctor X.ringCatSheaf x

/-- The stalk of a composite is the composite of the stalks. -/
private lemma stalkAb_map_comp {M N P : X.Modules} (f : M ⟶ N) (g : N ⟶ P) (x : X) :
    (stalkAb X x).map (f ≫ g) = (stalkAb X x).map f ≫ (stalkAb X x).map g :=
  Functor.map_comp _ _ _

/-- A composite whose first factor dies on the stalk at `x` dies there. -/
private lemma stalkAb_map_eq_zero_comp {M N P : X.Modules} (f : M ⟶ N) (g : N ⟶ P) (x : X)
    (h : (stalkAb X x).map f = 0) : (stalkAb X x).map (f ≫ g) = 0 :=
  (stalkAb_map_comp f g x).trans
    ((congrArg (fun t => t ≫ (stalkAb X x).map g) h).trans zero_comp)

/-- A composite which vanishes has vanishing composite of stalk maps. -/
private lemma stalkAb_map_comp_eq_zero {M N P : X.Modules} (f : M ⟶ N) (g : N ⟶ P) (x : X)
    (h : f ≫ g = 0) : (stalkAb X x).map f ≫ (stalkAb X x).map g = 0 :=
  (stalkAb_map_comp f g x).symm.trans
    ((congrArg (fun t => (stalkAb X x).map t) h).trans (Functor.map_zero _ _ _))

/-- The stalk of a composite, when the composite has been named. -/
private lemma stalkAb_map_eq_of_eq {M N P : X.Modules} (f : M ⟶ N) (g : N ⟶ P) {h : M ⟶ P}
    (hfg : f ≫ g = h) (x : X) :
    (stalkAb X x).map h = (stalkAb X x).map f ≫ (stalkAb X x).map g :=
  (congrArg (fun t => (stalkAb X x).map t) hfg).symm.trans (stalkAb_map_comp f g x)

/-- The first factor of a composite which is invertible on a stalk is invertible there as soon
as it is an epimorphism there. -/
private lemma isIso_stalkAb_first {M N P : X.Modules} (f : M ⟶ N) (g : N ⟶ P) {h : M ⟶ P}
    (hfg : f ≫ g = h) (x : X) (hepi : Epi ((stalkAb X x).map f))
    (hh : IsIso ((stalkAb X x).map h)) : IsIso ((stalkAb X x).map f) := by
  have : IsIso ((stalkAb X x).map f ≫ (stalkAb X x).map g) :=
    stalkAb_map_eq_of_eq f g hfg x ▸ hh
  have : Mono ((stalkAb X x).map f) :=
    mono_of_mono ((stalkAb X x).map f) ((stalkAb X x).map g)
  exact isIso_of_mono_of_epi _

/-- The second factor of a composite which is invertible on a stalk is invertible there as soon
as the first factor is. -/
private lemma isIso_stalkAb_second {M N P : X.Modules} (f : M ⟶ N) (g : N ⟶ P) {h : M ⟶ P}
    (hfg : f ≫ g = h) (x : X) (hf : IsIso ((stalkAb X x).map f))
    (hh : IsIso ((stalkAb X x).map h)) : IsIso ((stalkAb X x).map g) := by
  have : IsIso ((stalkAb X x).map f ≫ (stalkAb X x).map g) :=
    stalkAb_map_eq_of_eq f g hfg x ▸ hh
  exact IsIso.of_isIso_comp_left ((stalkAb X x).map f) ((stalkAb X x).map g)

/-- A monomorphism whose composite with something is an epimorphism on a stalk is invertible
there. -/
private lemma isIso_stalkAb_second_of_epi {M N P : X.Modules} (f : M ⟶ N) (g : N ⟶ P)
    {h : M ⟶ P} (hfg : f ≫ g = h) (x : X) (hepi : Epi ((stalkAb X x).map h))
    (hmono : Mono ((stalkAb X x).map g)) : IsIso ((stalkAb X x).map g) := by
  have : Epi ((stalkAb X x).map f ≫ (stalkAb X x).map g) :=
    stalkAb_map_eq_of_eq f g hfg x ▸ hepi
  have : Epi ((stalkAb X x).map g) :=
    epi_of_epi ((stalkAb X x).map f) ((stalkAb X x).map g)
  exact isIso_of_mono_of_epi _

/-- A monomorphism of modules is injective on every stalk. -/
private lemma mono_stalkAb_of_mono {M N : X.Modules} (f : M ⟶ N) (hf : Mono f) (x : X) :
    Mono ((stalkAb X x).map f) :=
  have := hf
  (AddCommGrpCat.mono_iff_injective ((stalkAb X x).map f)).mpr
    (stalk_map_injective_of_mono f x)

/-- An isomorphism of stalks over the local ring is one of the underlying abelian groups. -/
private lemma isIso_stalkAb_of_isIso_stalkMap {M N : X.Modules} (f : M ⟶ N) (x : X)
    (h : IsIso (SheafOfModules.stalkMap X.ringCatSheaf x f)) :
    IsIso ((stalkAb X x).map f) :=
  (ConcreteCategory.isIso_iff_bijective _).2
    ((ConcreteCategory.isIso_iff_bijective
      (SheafOfModules.stalkMap X.ringCatSheaf x f)).1 h)

/-- The stalk functor carries an epimorphism of sheaves of modules to an epimorphism: the
one-term complex it defines is exact, and exactness is detected on stalks. -/
private lemma epi_stalkAb_of_epi {M N : X.Modules} (f : M ⟶ N) [Epi f]
    (x : X) : Epi ((stalkAb X x).map f) := by
  let S : ShortComplex (SheafOfModules.{u} X.ringCatSheaf) :=
    ShortComplex.mk f (0 : N ⟶ N) comp_zero
  have hS : S.Exact := (ShortComplex.exact_iff_epi S rfl).mpr ‹Epi f›
  have hg : (SheafOfModules.stalkShortComplex X.ringCatSheaf S x).g = 0 :=
    Functor.map_zero (stalkAb X x) N N
  exact (ShortComplex.exact_iff_epi _ hg).mp
    ((SheafOfModules.exact_iff_stalkShortComplex_exact X.ringCatSheaf S).mp hS x)

/-- Where the stalk of the cokernel of `f` vanishes, `f` is an epimorphism on stalks. -/
private lemma epi_stalkAb_of_isZero_stalk_cokernel
    {M N : X.Modules} (f : M ⟶ N) (x : X)
    (h : IsZero ((stalkAb X x).obj (cokernel f))) : Epi ((stalkAb X x).map f) := by
  have hex := (SheafOfModules.exact_iff_stalkShortComplex_exact X.ringCatSheaf
    (ShortComplex.cokernelSequence f)).mp (ShortComplex.cokernelSequence_exact f) x
  exact (ShortComplex.exact_iff_epi _ (h.eq_zero_of_tgt _)).mp hex

/-- Where `f` is an isomorphism on stalks, the stalk of its cokernel vanishes. -/
private lemma isZero_stalk_cokernel_of_isIso_stalkAb
    {M N : X.Modules} (f : M ⟶ N) (x : X)
    (h : IsIso ((stalkAb X x).map f)) : IsZero ((stalkAb X x).obj (cokernel f)) := by
  have hepi : Epi ((stalkAb X x).map (cokernel.π f)) := epi_stalkAb_of_epi _ x
  have hcomp : (stalkAb X x).map f ≫ (stalkAb X x).map (cokernel.π f) = 0 :=
    stalkAb_map_comp_eq_zero f (cokernel.π f) x (cokernel.condition f)
  have hzero : (stalkAb X x).map (cokernel.π f) = 0 :=
    (cancel_epi ((stalkAb X x).map f)).mp (hcomp.trans comp_zero.symm)
  rw [IsZero.iff_id_eq_zero]
  refine (cancel_epi ((stalkAb X x).map (cokernel.π f))).mp ?_
  rw [hzero]
  exact zero_comp.trans zero_comp.symm

/-- The stalk of the inclusion of the kernel of `f` is the zero map wherever `f` is injective
on stalks. -/
private lemma stalkAb_kernel_ι_eq_zero {M N : X.Modules} (f : M ⟶ N)
    (x : X) (h : Mono ((stalkAb X x).map f)) :
    (stalkAb X x).map (kernel.ι f) = 0 := by
  refine (cancel_mono ((stalkAb X x).map f)).mp ?_
  exact (stalkAb_map_comp_eq_zero (kernel.ι f) f x (kernel.condition f)).trans zero_comp.symm

/-- A morphism of modules on a scheme which is invertible on every stalk is invertible. -/
private lemma isIso_of_forall_stalkAb_isIso {Y : Scheme.{u}} {M N : Y.Modules} (f : M ⟶ N)
    (h : ∀ y : Y, IsIso ((Scheme.Modules.toPresheaf Y ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y).map f)) : IsIso f := by
  let Ms : TopCat.Sheaf AddCommGrpCat.{u} Y := ⟨M.presheaf, M.isSheaf⟩
  let Ns : TopCat.Sheaf AddCommGrpCat.{u} Y := ⟨N.presheaf, N.isSheaf⟩
  let fs : Ms ⟶ Ns := ⟨f.mapPresheaf⟩
  have hstalks : ∀ y : Y,
      IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y).map fs.1) := fun y => by
    simpa [fs] using h y
  have hfs : IsIso fs := TopCat.Presheaf.isIso_of_stalkFunctor_map_iso fs
  have hmap : IsIso f.mapPresheaf := by
    change IsIso ((TopCat.Sheaf.forget AddCommGrpCat.{u} Y).map fs)
    infer_instance
  exact (isIso_iff_of_reflects_iso f (Scheme.Modules.toPresheaf Y)).mp (by
    simpa only [Scheme.Modules.toPresheaf_map, Scheme.Modules.toPresheaf_obj] using hmap)

/-- A morphism which is invertible on every stalk at a point of an open subset restricts to an
isomorphism over that open subset. -/
private lemma isIso_restrict_of_forall_stalkAb_isIso (W : X.Opens) {M N : X.Modules}
    (g : M ⟶ N) (hg : ∀ x : X, x ∈ (W : Set X) → IsIso ((stalkAb X x).map g)) :
    IsIso ((Scheme.Modules.restrictFunctor W.ι).map g) := by
  refine isIso_of_forall_stalkAb_isIso _ fun y => ?_
  let κ := Scheme.Modules.restrictStalkNatIso W.ι y
  let m₁ := (Scheme.Modules.toPresheaf (W : Scheme) ⋙
    TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y).map
      ((Scheme.Modules.restrictFunctor W.ι).map g)
  let m₂ := κ.hom.app N
  let m₃ := κ.hom.app M
  let m₄ := (Scheme.Modules.toPresheaf X ⋙
    TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (W.ι y)).map g
  have hnat : m₁ ≫ m₂ = m₃ ≫ m₄ := by
    simpa [m₁, m₂, m₃, m₄] using κ.hom.naturality g
  have : IsIso m₄ := hg (W.ι y) y.2
  have : IsIso (m₁ ≫ m₂) := by
    rw [hnat]
    infer_instance
  exact IsIso.of_isIso_comp_right m₁ m₂

/-! ### Support of a module on a scheme -/

/-- The support of a module on a scheme: the points whose stalk is nonzero. -/
private noncomputable def msupp (M : X.Modules) : Set X :=
  SheafOfModules.supp (M : SheafOfModules.{u} X.ringCatSheaf)

/-- A quotient of a module of finite type is of finite type, read at `X.Modules`. -/
public lemma isFiniteType_of_epi_modules {M N : X.Modules} (p : M ⟶ N)
    [Epi p] (hM : M.IsFiniteType) : N.IsFiniteType := by
  let M' : SheafOfModules X.ringCatSheaf := M
  let N' : SheafOfModules X.ringCatSheaf := N
  let p' : M' ⟶ N' := p
  have hp' : Epi p' := ‹Epi p›
  have hM' : SheafOfModules.IsFiniteType.{u, u, u} M' := hM
  exact Stacks.SheafOfModules.isFiniteType_of_epi.{u, u, u} p' hM'

/-- The support of a module of finite type on a scheme is closed. -/
private lemma isClosed_msupp (M : X.Modules) (hM : M.IsFiniteType) : IsClosed (msupp M) :=
  @SheafOfModules.isClosed_supp _ _ (M : SheafOfModules.{u} X.ringCatSheaf) hM

/-- A point outside the support has vanishing stalk. -/
private lemma isZero_stalkAb_of_notMem_msupp (M : X.Modules) (x : X) (h : x ∉ msupp M) :
    IsZero ((stalkAb X x).obj M) := by
  have hsub : Subsingleton ((stalkAb X x).obj M) :=
    not_nontrivial_iff_subsingleton.mp fun hn =>
      h ((SheafOfModules.mem_supp_iff_nontrivial_stalk
        (M : SheafOfModules.{u} X.ringCatSheaf) x).mpr hn)
  exact AddCommGrpCat.isZero_of_subsingleton _

/-- A point with vanishing stalk is outside the support. -/
private lemma notMem_msupp_of_isZero_stalkAb (M : X.Modules) (x : X)
    (h : IsZero ((stalkAb X x).obj M)) : x ∉ msupp M := fun hx =>
  (not_nontrivial_iff_subsingleton.mpr (AddCommGrpCat.isZero_iff_subsingleton.mp h))
    ((SheafOfModules.mem_supp_iff_nontrivial_stalk
      (M : SheafOfModules.{u} X.ringCatSheaf) x).mp hx)

/-! ### Depth at least one and associated points -/

/-- A point at which a coherent module has depth at least one is not an associated point. -/
private lemma notMem_associatedPoints_of_one_le_depth (H : X.Modules)
    [SheafOfModules.IsCoherent H] (x : X)
    (hdepth :
      letI : Module (X.presheaf.stalk x)
          (TopCat.Presheaf.stalk (C := Ab.{u}) H.val.presheaf x) :=
        PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
          (R := X.presheaf) H.val x
      (1 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x)
        (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
        (TopCat.Presheaf.stalk (C := Ab.{u}) H.val.presheaf x)) :
    x ∉ Stacks.Divisors.associatedPoints H := by
  intro hxass
  rw [Stacks.Divisors.mem_associatedPoints_iff] at hxass
  let : Module (X.presheaf.stalk x)
      (TopCat.Presheaf.stalk (C := Ab.{u}) H.val.presheaf x) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := X.presheaf) H.val x
  let : H.IsFiniteType := SheafOfModules.IsCoherent.isFiniteType
  let : Module.Finite (X.presheaf.stalk x)
      (TopCat.Presheaf.stalk (C := Ab.{u}) H.val.presheaf x) :=
    SheafOfModules.finite_stalk X.sheaf H x
  exact maximalIdeal_not_isAssociatedPrimeStacks_of_one_le_depth hdepth hxass

/-- A map to a quasi-coherent module on a locally Noetherian scheme vanishes as soon as its
stalk map vanishes at every associated point of the target. -/
private lemma hom_eq_zero_of_stalkAb_eq_zero_on_associatedPoints [IsLocallyNoetherian X]
    {K H : X.Modules} [H.IsQuasicoherent] (g : K ⟶ H)
    (h : ∀ x : X, x ∈ Stacks.Divisors.associatedPoints H → (stalkAb X x).map g = 0) :
    g = 0 := by
  ext V s
  refine eq_zero_of_forall_germ_associatedPoints_eq_zero H V _ fun x hx hxass => ?_
  have hgerm := TopCat.Presheaf.stalkFunctor_map_germ_apply (C := AddCommGrpCat.{u}) V x hx
    ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map g.val) s
  have hgerm' : (ConcreteCategory.hom (H.presheaf.germ V x hx))
      ((ConcreteCategory.hom (Scheme.Modules.Hom.app g V)) s) =
      (ConcreteCategory.hom ((stalkAb X x).map g))
        ((ConcreteCategory.hom (K.presheaf.germ V x hx)) s) := hgerm.symm
  rw [hgerm', h x hxass]
  rfl

/-- A map vanishes on the kernel of `φ` as soon as `φ` is invertible on stalks off `T` and no
associated point of its quasi-coherent target lies in `T`. -/
private lemma kernel_ι_comp_eq_zero_of_notMem_associatedPoints [IsLocallyNoetherian X] (T : Set X)
    {F G H : X.Modules} [H.IsQuasicoherent] (φ : F ⟶ G) (ψ : F ⟶ H)
    (hφ : ∀ x : X, x ∉ T → IsIso ((stalkAb X x).map φ))
    (hH : ∀ x : X, x ∈ T → x ∉ Stacks.Divisors.associatedPoints H) : kernel.ι φ ≫ ψ = 0 := by
  refine hom_eq_zero_of_stalkAb_eq_zero_on_associatedPoints _ fun x hxass => ?_
  have := hφ x fun hxT => hH x hxT hxass
  exact stalkAb_map_eq_zero_comp _ ψ x (stalkAb_kernel_ι_eq_zero φ x inferInstance)

/-- The open subset where the cokernels of two maps to modules of finite type both have
vanishing stalks. -/
private lemma exists_opens_isZero_stalkAb_cokernel {F G H : X.Modules} (φ : F ⟶ G) (ψ : F ⟶ H)
    (hG : G.IsFiniteType) (hH : H.IsFiniteType) :
    ∃ W : X.Opens, ∀ x : X, x ∈ (W : Set X) ↔
      IsZero ((stalkAb X x).obj (cokernel φ)) ∧ IsZero ((stalkAb X x).obj (cokernel ψ)) :=
  ⟨⟨(msupp (cokernel φ) ∪ msupp (cokernel ψ))ᶜ,
    ((isClosed_msupp _ (isFiniteType_of_epi_modules (cokernel.π φ) hG)).union
      (isClosed_msupp _ (isFiniteType_of_epi_modules (cokernel.π ψ) hH))).isOpen_compl⟩,
    fun x => ⟨fun h => ⟨isZero_stalkAb_of_notMem_msupp _ x fun h₁ => h (Or.inl h₁),
      isZero_stalkAb_of_notMem_msupp _ x fun h₂ => h (Or.inr h₂)⟩,
      fun h hmem => hmem.elim (notMem_msupp_of_isZero_stalkAb _ x h.1)
        (notMem_msupp_of_isZero_stalkAb _ x h.2)⟩⟩

/-- **Hartogs.** The unit of the restriction adjunction along an open subset is an isomorphism
at a coherent module whose stalks have depth at least two off that open subset. -/
private theorem isIso_restrictAdjunction_unit_of_two_le_depth [IsLocallyNoetherian X] (W : X.Opens)
    (M : X.Modules) [M.IsCoherent]
    (hdepth : ∀ x : X, x ∉ (W : Set X) →
      letI : Module (X.presheaf.stalk x)
          (TopCat.Presheaf.stalk (C := Ab.{u}) M.val.presheaf x) :=
        PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
          (R := X.presheaf) M.val x
      (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x)
        (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
        (TopCat.Presheaf.stalk (C := Ab.{u}) M.val.presheaf x)) :
    IsIso ((Scheme.Modules.restrictAdjunction W.ι).unit.app M) := by
  have hP : IsIso ((Scheme.Modules.pullbackPushforwardAdjunction W.ι).unit.app M) :=
    isIso_unit_restrict_pushforward_of_depth_ge_two X M W hdepth
  have hcomp : (Scheme.Modules.restrictAdjunction W.ι).unit.app M ≫
      (Scheme.Modules.pushforward W.ι).map
        ((Scheme.Modules.restrictFunctorIsoPullback W.ι).hom.app M) =
      (Scheme.Modules.pullbackPushforwardAdjunction W.ι).unit.app M :=
    Adjunction.unit_leftAdjointUniq_hom_app _ _ M
  have : IsIso ((Scheme.Modules.restrictAdjunction W.ι).unit.app M ≫
      (Scheme.Modules.pushforward W.ι).map
        ((Scheme.Modules.restrictFunctorIsoPullback W.ι).hom.app M)) := by
    rwa [hcomp]
  exact IsIso.of_isIso_comp_right ((Scheme.Modules.restrictAdjunction W.ι).unit.app M)
    ((Scheme.Modules.pushforward W.ι).map
      ((Scheme.Modules.restrictFunctorIsoPullback W.ι).hom.app M))

/-- If each of two maps out of `F` kills the kernel of the other, the second factors through
the coimage of the first by a monomorphism. -/
private theorem _root_.CategoryTheory.Abelian.exists_mono_of_kernel_ι_comp_eq_zero {C : Type*}
    [Category C] [Abelian C] {F G H : C} (φ : F ⟶ G) (ψ : F ⟶ H)
    (hψ : kernel.ι φ ≫ ψ = 0) (hφ : kernel.ι ψ ≫ φ = 0) :
    ∃ b : Abelian.coimage φ ⟶ H, Abelian.coimage.π φ ≫ b = ψ ∧ Mono b := by
  have hθ : kernel.ι φ ≫ Abelian.coimage.π ψ = 0 := Abelian.comp_coimage_π_eq_zero hψ
  have hθ' : kernel.ι ψ ≫ Abelian.coimage.π φ = 0 := Abelian.comp_coimage_π_eq_zero hφ
  refine ⟨cokernel.desc (kernel.ι φ) (Abelian.coimage.π ψ) hθ ≫
    Abelian.factorThruCoimage ψ, ?_, ?_⟩
  · rw [← Category.assoc, cokernel.π_desc, Abelian.coimage.fac]
  · have : IsIso (cokernel.desc (kernel.ι φ) (Abelian.coimage.π ψ) hθ) := by
      refine ⟨cokernel.desc (kernel.ι ψ) (Abelian.coimage.π φ) hθ', ?_, ?_⟩
      · refine (cancel_epi (Abelian.coimage.π φ)).mp ?_
        rw [← Category.assoc, cokernel.π_desc, cokernel.π_desc, Category.comp_id]
      · refine (cancel_epi (Abelian.coimage.π ψ)).mp ?_
        rw [← Category.assoc, cokernel.π_desc, cokernel.π_desc, Category.comp_id]
    exact mono_comp _ _

/-! ### The comparison isomorphism over an open subset -/

/-- Two maps out of a module which both factor through one quotient-like object `Q`, by maps
becoming isomorphisms after restriction to `W`, have uniquely isomorphic targets as soon as
each target is the pushforward of its restriction to `W`. -/
private lemma existsUnique_iso_of_restrict (W : X.Opens) {F G H Q : X.Modules}
    (φ : F ⟶ G) (ψ : F ⟶ H) (q : F ⟶ Q) (a : Q ⟶ G) (b : Q ⟶ H)
    (hqa : q ≫ a = φ) (hqb : q ≫ b = ψ) (hq : Epi q)
    (haW : IsIso ((Scheme.Modules.restrictFunctor W.ι).map a))
    (hbW : IsIso ((Scheme.Modules.restrictFunctor W.ι).map b))
    (hunitG : IsIso ((Scheme.Modules.restrictAdjunction W.ι).unit.app G))
    (hunitH : IsIso ((Scheme.Modules.restrictAdjunction W.ι).unit.app H)) :
    ∃! e : G ≅ H, φ ≫ e.hom = ψ := by
  have hLq : Epi ((Scheme.Modules.restrictFunctor W.ι).map q) := by
    have := hq
    infer_instance
  have key : ∀ {M N : X.Modules} (f : M ⟶ N),
      f ≫ (Scheme.Modules.restrictAdjunction W.ι).unit.app N =
        (Scheme.Modules.restrictAdjunction W.ι).unit.app M ≫
          (Scheme.Modules.pushforward W.ι).map
            ((Scheme.Modules.restrictFunctor W.ι).map f) := fun f =>
    (Scheme.Modules.restrictAdjunction W.ι).unit.naturality f
  obtain ⟨ζ, hζ, hζiso⟩ : ∃ ζ : (Scheme.Modules.restrictFunctor W.ι).obj G ⟶
      (Scheme.Modules.restrictFunctor W.ι).obj H,
      ((Scheme.Modules.restrictFunctor W.ι).map a ≫ ζ =
        (Scheme.Modules.restrictFunctor W.ι).map b) ∧ IsIso ζ := by
    refine ⟨inv ((Scheme.Modules.restrictFunctor W.ι).map a) ≫
      (Scheme.Modules.restrictFunctor W.ι).map b, ?_, ?_⟩
    · rw [IsIso.hom_inv_id_assoc]
    · infer_instance
  have hLφζ : (Scheme.Modules.restrictFunctor W.ι).map φ ≫ ζ =
      (Scheme.Modules.restrictFunctor W.ι).map ψ := by
    rw [← hqa, ← hqb, Functor.map_comp, Functor.map_comp, Category.assoc, hζ]
  have hLφepi : Epi ((Scheme.Modules.restrictFunctor W.ι).map φ) := by
    rw [← hqa, Functor.map_comp]
    have := haW
    exact epi_comp _ _
  obtain ⟨e, he, heiso⟩ : ∃ e : G ⟶ H,
      (e ≫ (Scheme.Modules.restrictAdjunction W.ι).unit.app H =
        (Scheme.Modules.restrictAdjunction W.ι).unit.app G ≫
          (Scheme.Modules.pushforward W.ι).map ζ) ∧ IsIso e := by
    refine ⟨(Scheme.Modules.restrictAdjunction W.ι).unit.app G ≫
      (Scheme.Modules.pushforward W.ι).map ζ ≫
        inv ((Scheme.Modules.restrictAdjunction W.ι).unit.app H), ?_, ?_⟩
    · rw [Category.assoc, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    · infer_instance
  have heq : φ ≫ e = ψ := by
    refine (cancel_mono ((Scheme.Modules.restrictAdjunction W.ι).unit.app H)).mp ?_
    rw [Category.assoc, he, ← Category.assoc, key φ, Category.assoc, ← Functor.map_comp,
      hLφζ, key ψ]
  have hLc : ∀ c : G ⟶ H, φ ≫ c = ψ → (Scheme.Modules.restrictFunctor W.ι).map c = ζ :=
    fun c hc => (cancel_epi ((Scheme.Modules.restrictFunctor W.ι).map φ)).mp
      (by rw [hLφζ, ← Functor.map_comp, hc])
  refine ⟨asIso e, heq, fun c hc => Iso.ext ?_⟩
  change c.hom = e
  refine (cancel_mono ((Scheme.Modules.restrictAdjunction W.ι).unit.app H)).mp ?_
  rw [key c.hom, key e, hLc _ hc, hLc e heq]

/-! ### The depth-two extension property and its uniqueness -/

/-- A coherent map unchanged outside `T` and having depth at least two on `T`. -/
public def IsDepthTwoExtension {X : Scheme.{u}} (T : Set X)
    {F G : X.Modules} (φ : F ⟶ G) : Prop :=
  G.IsCoherent ∧
    (∀ x : X, x ∉ T →
      IsIso (AlgebraicGeometry.SheafOfModules.stalkMap X.ringCatSheaf x φ)) ∧
    (∀ x : X, x ∈ T →
      let M := TopCat.Presheaf.stalk (C := Ab.{u}) G.val.presheaf x
      letI : Module (X.presheaf.stalk x) M :=
        PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
          G.val x
      (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x)
        (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) M)

/-- Two depth-two extensions of a module along a subset are isomorphic by a unique isomorphism
compatible with the two maps. -/
public theorem depthTwoExtension_unique
    (X : Scheme.{u}) [IsNoetherian X]
    (T : Set X)
    (F G H : X.Modules) (φ : F ⟶ G) (ψ : F ⟶ H)
    (hφ : IsDepthTwoExtension T φ) (hψ : IsDepthTwoExtension T ψ) :
    ∃! e : G ≅ H, φ ≫ e.hom = ψ := by
  have hGc : G.IsCoherent := hφ.1
  have hHc : H.IsCoherent := hψ.1
  have hGq : G.IsQuasicoherent :=
    (Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent G).1
  have hHq : H.IsQuasicoherent :=
    (Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent H).1
  have hGf : G.IsFiniteType := SheafOfModules.IsCoherent.isFiniteType
  have hHf : H.IsFiniteType := SheafOfModules.IsCoherent.isFiniteType
  have hφiso : ∀ x : X, x ∉ T → IsIso ((stalkAb X x).map φ) := fun x hx =>
    isIso_stalkAb_of_isIso_stalkMap φ x (hφ.2.1 x hx)
  have hψiso : ∀ x : X, x ∉ T → IsIso ((stalkAb X x).map ψ) := fun x hx =>
    isIso_stalkAb_of_isIso_stalkMap ψ x (hψ.2.1 x hx)
  have hGass : ∀ x : X, x ∈ T → x ∉ Stacks.Divisors.associatedPoints G := fun x hx =>
    notMem_associatedPoints_of_one_le_depth G x (le_trans (by norm_num) (hφ.2.2 x hx))
  have hHass : ∀ x : X, x ∈ T → x ∉ Stacks.Divisors.associatedPoints H := fun x hx =>
    notMem_associatedPoints_of_one_le_depth H x (le_trans (by norm_num) (hψ.2.2 x hx))
  obtain ⟨b, hqb, hmonob⟩ := Abelian.exists_mono_of_kernel_ι_comp_eq_zero φ ψ
    (kernel_ι_comp_eq_zero_of_notMem_associatedPoints T φ ψ hφiso hHass)
    (kernel_ι_comp_eq_zero_of_notMem_associatedPoints T ψ φ hψiso hGass)
  have hqa : Abelian.coimage.π φ ≫ Abelian.factorThruCoimage φ = φ := Abelian.coimage.fac φ
  have hepiq : Epi (Abelian.coimage.π φ) := by
    change Epi (cokernel.π (kernel.ι φ))
    infer_instance
  obtain ⟨W, hWmem⟩ := exists_opens_isZero_stalkAb_cokernel φ ψ hGf hHf
  have hWT : ∀ x : X, x ∉ (W : Set X) → x ∈ T := fun x hx =>
    Classical.byContradiction fun hxT => hx ((hWmem x).mpr
      ⟨isZero_stalk_cokernel_of_isIso_stalkAb φ x (hφiso x hxT),
        isZero_stalk_cokernel_of_isIso_stalkAb ψ x (hψiso x hxT)⟩)
  have haisoW : ∀ x : X, x ∈ (W : Set X) →
      IsIso ((stalkAb X x).map (Abelian.factorThruCoimage φ)) := fun x hx =>
    isIso_stalkAb_second_of_epi (Abelian.coimage.π φ) (Abelian.factorThruCoimage φ) hqa x
      (epi_stalkAb_of_isZero_stalk_cokernel φ x ((hWmem x).mp hx).1)
      (mono_stalkAb_of_mono (Abelian.factorThruCoimage φ) inferInstance x)
  have hbisoW : ∀ x : X, x ∈ (W : Set X) → IsIso ((stalkAb X x).map b) := fun x hx =>
    isIso_stalkAb_second_of_epi (Abelian.coimage.π φ) b hqb x
      (epi_stalkAb_of_isZero_stalk_cokernel ψ x ((hWmem x).mp hx).2)
      (mono_stalkAb_of_mono b hmonob x)
  exact existsUnique_iso_of_restrict W φ ψ (Abelian.coimage.π φ)
    (Abelian.factorThruCoimage φ) b hqa hqb hepiq
    (isIso_restrict_of_forall_stalkAb_isIso W _ haisoW)
    (isIso_restrict_of_forall_stalkAb_isIso W b hbisoW)
    (isIso_restrictAdjunction_unit_of_two_le_depth W G fun x hx => hφ.2.2 x (hWT x hx))
    (isIso_restrictAdjunction_unit_of_two_le_depth W H fun x hx => hψ.2.2 x (hWT x hx))

end AlgebraicGeometry

end
