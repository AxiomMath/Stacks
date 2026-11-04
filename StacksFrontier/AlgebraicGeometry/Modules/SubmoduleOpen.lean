module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import StacksFrontier.AlgebraicGeometry.AffineQcohPushforward.Colimits
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.Completion.IdealPowerQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Modules.IdealPowerMultiple
public import StacksFrontier.AlgebraicGeometry.Modules.QuasicoherentLocal
public import StacksFrontier.AlgebraicGeometry.QcohLimits.Basic
public import StacksFrontier.AlgebraicGeometry.QcohPushforwardOpen.Basic
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.GraphKernelRestriction

/-!
# Submodules of a module on a scheme, read over an open

This module collects the operations on submodules of an `𝒪_X`-module that a local-to-global
gluing argument needs and the library does not have.

The first is the *image* of a morphism as a submodule of its target. A morphism of sheaves of
modules has a sectionwise image, and that image is a subsheaf even though the image presheaf of a
morphism of sheaves is in general not: the image over an open is the kernel of the projection to
the cokernel, because evaluation at an open preserves kernels, so `M ⟶ N ⟶ N / M` is exact on
sections even though `N ⟶ N / M` is only locally surjective.

The second is the *comap along an open*: given a submodule `K` of `M` and an open `V`, the
sections over `W` whose restriction to `W ⊓ V` lies in `K` form a submodule `K.comapOpen V`. It is
the largest submodule of `M` agreeing with `K` over `V`, so it is the universal receptacle for an
extension of `K` from `V` to the whole of `X`, and membership in it is decided by the restriction
to `V` — which is what makes it stable under gluing along a family of opens.

The third is a criterion for a submodule to be quasi-coherent over a union of opens: a submodule
`L` which over each member of a family of opens is contained in, and agrees with, a submodule
that is quasi-coherent there is quasi-coherent over the union of the family. This is what lets a
submodule assembled out of local pieces be recognised as quasi-coherent.

## Main definitions

* `AlgebraicGeometry.imageSubmodule` — the sectionwise image of a morphism of `𝒪_X`-modules, as a
  submodule of its target.
* `SheafOfModules.Submodule.comapOpen` — the sections whose restriction to an open lies in a given
  submodule.
* `AlgebraicGeometry.submoduleHomOfLE` — the inclusion of one submodule into a larger one, typed
  at `X.Modules` rather than at `SheafOfModules X.ringCatSheaf`.

## Main results

* `AlgebraicGeometry.cokernel_π_val_app_eq_zero_iff` — a section dies in the cokernel of a
  monomorphism exactly when it is in the image on sections.
* `AlgebraicGeometry.imageSubmodule_obj` and `AlgebraicGeometry.isQuasicoherent_imageSubmodule` —
  the sections of the image submodule, and its quasi-coherence.
* `SheafOfModules.Submodule.le_comapOpen`, `SheafOfModules.Submodule.comapOpen_obj_of_le` and
  `SheafOfModules.Submodule.mem_comapOpen_of_mem_inf` — the comap along an open contains the
  submodule it comes from, agrees with it there, and has membership decided over that open.
* `AlgebraicGeometry.isQuasicoherent_restrict_iSup_of_agree` — the quasi-coherence criterion over
  a union described above.
* `AlgebraicGeometry.kernelSubmodule_id_obj` — the submodule with no sections, through which the
  locality of vanishing is applied, and `AlgebraicGeometry.mem_submodule_of_locally_mem`, that
  locality itself.
* `AlgebraicGeometry.submodule_inf_obj` and `AlgebraicGeometry.mem_iInf_submodule_obj` — the
  sections of an intersection and of an infimum of submodules.
* `AlgebraicGeometry.isIso_restrictFunctor_map_submoduleHomOfLE` and
  `AlgebraicGeometry.isQuasicoherent_restrict_of_le_of_agree` — two nested submodules agreeing
  over an open have the same restriction there, so quasi-coherence passes between them.

## Implementation notes

Everything is phrased on sections over opens of `X`, never on a module restricted to an open
subscheme, so no identification of an open of an open subscheme with an open of `X` occurs. The
one place where restriction to an open subscheme is unavoidable is quasi-coherence, which is a
property of a module and not of a family of modules of sections; there the comparison is made at
the level of *modules*, by the inclusion of one submodule in another becoming invertible after
restriction, and never at the level of submodules.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe w u

namespace AlgebraicGeometry

attribute [local instance_reducible] AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-! ### Restriction of sections along an inclusion of opens -/

/-- Any two restriction maps between the same two opens agree: a poset has at most one morphism
between two objects. -/
theorem val_map_congr {M : X.Modules} {W W' : (Opens X)ᵒᵖ} (f g : W ⟶ W') (s : M.val.obj W) :
    M.val.map f s = M.val.map g s :=
  PresheafOfModules.congr_map_apply M.val (Subsingleton.elim f g) s

/-- Restricting a section twice is restricting it once. -/
theorem val_map_map {M : X.Modules} {W W' W'' : (Opens X)ᵒᵖ} (f : W ⟶ W') (g : W' ⟶ W'')
    (s : M.val.obj W) (h : W ⟶ W'') :
    M.val.map g (M.val.map f s) = M.val.map h s :=
  (PresheafOfModules.map_comp_apply M.val f g s).symm.trans (val_map_congr _ _ s)

/-- Restricting a section to the open it is already defined on does nothing. -/
theorem val_map_id {M : X.Modules} {W : (Opens X)ᵒᵖ} (h : W ⟶ W) (s : M.val.obj W) :
    M.val.map h s = s := by
  rw [val_map_congr h (𝟙 W) s, M.val.map_id]
  rfl

/-- The restriction of a section of a submodule is a section of that submodule. -/
theorem val_map_mem_submodule {M : X.Modules} (K : M.Submodule) {W W' : (Opens X)ᵒᵖ}
    (f : W ⟶ W') {s : M.val.obj W} (hs : s ∈ K.toSubmodule.obj W) :
    M.val.map f s ∈ K.toSubmodule.obj W' :=
  K.toSubmodule.map_mem f hs

/-! ### Sections of a cokernel -/

/-- A section of `N` over an open dies in the cokernel of a monomorphism `p : M ⟶ N` exactly when
it is in the image of the sections of `p` over that open.

Evaluation at an open preserves zero morphisms and finite limits, so it carries the exact sequence
`M ⟶ N ⟶ N / M` to an exact sequence of modules; exactness there is the statement that the kernel
of the second map is the image of the first. -/
theorem cokernel_π_val_app_eq_zero_iff {M N : X.Modules} (p : M ⟶ N) (hp : Mono p)
    (U : X.Opens) (s : Γ(N, U)) :
    (cokernel.π (C := X.Modules) p).val.app (op U) s = 0 ↔
      ∃ t : Γ(M, U), (p.val.app (op U)) t = s := by
  let T : X.Modules ⥤ ModuleCat Γ(X, U) := SheafOfModules.evaluation X.ringCatSheaf (op U)
  let _ : T.PreservesZeroMorphisms := ⟨by intros; rfl⟩
  let _ : PreservesFiniteLimits T :=
    SheafOfModules.Finite.evaluationPreservesFiniteLimits X.ringCatSheaf (op U)
  have hh := (ShortComplex.moduleCat_exact_iff _).mp
    ((ShortComplex.exact_cokernel (C := X.Modules) p).map_of_mono_of_preservesKernel T
      inferInstance inferInstance)
  refine ⟨hh s, ?_⟩
  rintro ⟨t, rfl⟩
  exact congrArg (fun f : M ⟶ cokernel (C := X.Modules) p => f.val.app (op U) t)
    (cokernel.condition (C := X.Modules) p)

/-! ### The image of a morphism as a submodule -/

/-- The sectionwise image of a morphism of `𝒪_X`-modules, as a submodule of its target: the
sections killed by the projection to the cokernel. -/
def imageSubmodule {M N : X.Modules} (p : M ⟶ N) : N.Submodule :=
  Stacks.Algebraization.kernelSubmodule (cokernel.π (C := X.Modules) p)

/-- The sections of the image submodule of a monomorphism over an open are the image of its
sections. -/
theorem imageSubmodule_obj {M N : X.Modules} (p : M ⟶ N) (hp : Mono p) (U : X.Opens) :
    (imageSubmodule p).toSubmodule.obj (op U) = LinearMap.range (p.val.app (op U)).hom := by
  rw [imageSubmodule, Stacks.Algebraization.kernelSubmodule_toSubmodule_obj]
  ext s
  rw [LinearMap.mem_ker, LinearMap.mem_range]
  exact cokernel_π_val_app_eq_zero_iff p hp U s

/-- The sectionwise kernel of a morphism of quasi-coherent modules is quasi-coherent. -/
private theorem isQuasicoherent_kernelSubmodule {M N : X.Modules} (ψ : M ⟶ N)
    [M.IsQuasicoherent] [N.IsQuasicoherent] :
    (Stacks.Algebraization.kernelSubmodule ψ).toSheafOfModules.IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    (Stacks.Algebraization.kernelSubmoduleIso ψ).symm
    (Stacks.AlgebraicGeometry.QcohLimits.isQuasicoherent_kernel _)

/-- The image submodule of a morphism of quasi-coherent modules is quasi-coherent. -/
theorem isQuasicoherent_imageSubmodule {M N : X.Modules} (p : M ⟶ N) [M.IsQuasicoherent]
    [N.IsQuasicoherent] : (imageSubmodule p).toSheafOfModules.IsQuasicoherent :=
  isQuasicoherent_kernelSubmodule _


/-! ### Intersections and vanishing of quasi-coherent submodules -/

/-- The sections of an intersection of two submodules are the intersection of their sections. -/
theorem submodule_inf_obj {M : X.Modules} (P Q : M.Submodule) (W : (Opens X)ᵒᵖ) :
    (P ⊓ Q).toSubmodule.obj W = P.toSubmodule.obj W ⊓ Q.toSubmodule.obj W := rfl

/-- A section lies in an infimum of submodules exactly when it lies in each of them. -/
theorem mem_iInf_submodule_obj {M : X.Modules} {I : Type w} (N : I → M.Submodule)
    (W : (Opens X)ᵒᵖ) (s : M.val.obj W) :
    s ∈ (⨅ i, N i).toSubmodule.obj W ↔ ∀ i, s ∈ (N i).toSubmodule.obj W := by
  rw [SheafOfModules.Submodule.toSubmodule_iInf, iInf, PresheafOfModules.Submodule.sInf_obj]
  simp [_root_.Submodule.mem_iInf]

/-- **Membership in a submodule of a sheaf of modules is local.** A section lying in the submodule
on a neighbourhood of every point of its open lies in it. This is the `isSheaf` field of a
submodule, in the form its consumers use. -/
theorem mem_submodule_of_locally_mem {M : X.Modules} (N : M.Submodule) (W : X.Opens)
    (s : Γ(M, W))
    (h : ∀ x ∈ W, ∃ (W' : X.Opens) (hW' : W' ≤ W), x ∈ W' ∧
      M.val.map (CategoryTheory.homOfLE hW').op s ∈ N.toSubmodule.obj (op W')) :
    s ∈ N.toSubmodule.obj (op W) :=
  N.isSheaf s fun x hx => by
    obtain ⟨W', hW', hxW', hmem⟩ := h x hx
    exact ⟨W', CategoryTheory.homOfLE hW', hmem, hxW'⟩

/-- A section lies in the sectionwise kernel of a morphism exactly when the morphism kills it. -/
theorem mem_kernelSubmodule_iff {M N : X.Modules} (f : M ⟶ N) (W : X.Opens) (s : Γ(M, W)) :
    s ∈ (Stacks.Algebraization.kernelSubmodule f).toSubmodule.obj (op W) ↔
      (f.val.app (op W)) s = 0 := by
  rw [Stacks.Algebraization.kernelSubmodule_toSubmodule_obj]
  exact Iff.rfl

/-- The sections of a submodule are the image of the sections of its inclusion. -/
theorem range_submodule_ι_app {M : X.Modules} (P : M.Submodule) (W : X.Opens) :
    LinearMap.range (P.ι.val.app (op W)).hom = P.toSubmodule.obj (op W) :=
  _root_.Submodule.range_subtype _

/-- The intersection of a quasi-coherent submodule with the sectionwise kernel of a morphism to a
quasi-coherent module is quasi-coherent: it is the image of the kernel of the morphism restricted
to that submodule. -/
theorem isQuasicoherent_inf_kernelSubmodule {M N : X.Modules} [M.IsQuasicoherent]
    [N.IsQuasicoherent] (P : M.Submodule) (hP : P.toSheafOfModules.IsQuasicoherent)
    (ψ : M ⟶ N) :
    (P ⊓ Stacks.Algebraization.kernelSubmodule ψ).toSheafOfModules.IsQuasicoherent := by
  have : (P.toSheafOfModules : X.Modules).IsQuasicoherent := hP
  set ψ' : (P.toSheafOfModules : X.Modules) ⟶ N := P.ι ≫ ψ with hψ'
  have := isQuasicoherent_kernelSubmodule ψ'
  set p : ((Stacks.Algebraization.kernelSubmodule ψ').toSheafOfModules : X.Modules) ⟶ M :=
    (Stacks.Algebraization.kernelSubmodule ψ').ι ≫ P.ι with hp
  have h3 : Mono p := by rw [hp]; infer_instance
  have heq : P ⊓ Stacks.Algebraization.kernelSubmodule ψ = imageSubmodule p := by
    refine SheafOfModules.Submodule.ext (PresheafOfModules.Submodule.ext fun W => ?_)
    obtain ⟨W, rfl⟩ : ∃ W₀ : X.Opens, op W₀ = W := ⟨W.unop, rfl⟩
    rw [imageSubmodule_obj p h3 W]
    refine le_antisymm (fun s hs => ?_) (fun s hs => ?_)
    · obtain ⟨hsP, hsk⟩ := hs
      refine ⟨⟨⟨s, hsP⟩, (mem_kernelSubmodule_iff ψ' W _).2 ?_⟩, rfl⟩
      exact (mem_kernelSubmodule_iff ψ W s).1 hsk
    · obtain ⟨t, rfl⟩ := hs
      have ht := (mem_kernelSubmodule_iff ψ' W t.1).1 t.2
      exact ⟨t.1.2, (mem_kernelSubmodule_iff ψ W _).2 ht⟩
  rw [heq]
  exact isQuasicoherent_imageSubmodule _

/-- The sectionwise kernel of the identity has no sections. It is the receptacle for the locality
of vanishing: a section lies in it exactly when it is zero, and membership in a submodule of a
sheaf of modules is local, whereas the bottom of the submodule lattice is an infimum whose
sections are not read off directly. -/
theorem kernelSubmodule_id_obj (M : X.Modules) (W : (Opens X)ᵒᵖ) :
    (Stacks.Algebraization.kernelSubmodule (𝟙 M)).toSubmodule.obj W = ⊥ := by
  rw [Stacks.Algebraization.kernelSubmodule_toSubmodule_obj]
  refine le_antisymm (fun s hs => ?_) bot_le
  rw [LinearMap.mem_ker] at hs
  exact hs

/-- A quasi-coherent submodule whose sections over an affine open vanish has vanishing sections
over every basic open of that affine open: the sections over a basic open are a localization of
the sections over the affine open. -/
private theorem submodule_obj_basicOpen_eq_bot {M : X.Modules} [M.IsQuasicoherent]
    (P : M.Submodule) (hP : P.toSheafOfModules.IsQuasicoherent) {W : X.Opens}
    (hW : IsAffineOpen W) (hPW : P.toSubmodule.obj (op W) = ⊥) (g : Γ(X, W)) :
    P.toSubmodule.obj (op (X.basicOpen g)) = ⊥ := by
  have : (P.toSheafOfModules : X.Modules).IsQuasicoherent := hP
  have hle : X.basicOpen g ≤ W := X.basicOpen_le g
  let _hmod := Stacks.AlgebraicGeometry.QuasicoherentBaseChange.moduleOfLE
    (P.toSheafOfModules : X.Modules) hle
  have hloc : IsLocalizedModule.Away g
      (Stacks.AlgebraicGeometry.QuasicoherentBaseChange.restrictₗ
        (P.toSheafOfModules : X.Modules) hle) :=
    Stacks.AlgebraicGeometry.QcohPushforwardOpen.isLocalizedModule_restrictₗ_of_eq
      (P.toSheafOfModules : X.Modules) hW.isCompact hW.isQuasiSeparated g rfl hle
  have hsub : Subsingleton Γ((P.toSheafOfModules : X.Modules), W) := by
    refine ⟨fun a b => Subtype.ext ?_⟩
    rw [show a.1 = 0 from (_root_.Submodule.mem_bot _).1 (hPW.le a.2),
      show b.1 = 0 from (_root_.Submodule.mem_bot _).1 (hPW.le b.2)]
  refine le_antisymm (fun s hs => ?_) bot_le
  have _hloc := hloc
  obtain ⟨⟨x, t⟩, ht⟩ := IsLocalizedModule.surj (Submonoid.powers g)
    (Stacks.AlgebraicGeometry.QuasicoherentBaseChange.restrictₗ
      (P.toSheafOfModules : X.Modules) hle)
    (⟨s, hs⟩ : Γ((P.toSheafOfModules : X.Modules), X.basicOpen g))
  rw [show x = 0 from hsub.elim x 0, map_zero] at ht
  have hy : (⟨s, hs⟩ : Γ((P.toSheafOfModules : X.Modules), X.basicOpen g)) = 0 :=
    IsLocalizedModule.smul_injective
      (Stacks.AlgebraicGeometry.QuasicoherentBaseChange.restrictₗ
        (P.toSheafOfModules : X.Modules) hle) t (ht.trans (smul_zero _).symm)
  exact (_root_.Submodule.mem_bot _).2 (congrArg Subtype.val hy)

/-- **Vanishing of a quasi-coherent submodule spreads from an affine open to its opens.** A
quasi-coherent submodule whose sections over an affine open vanish has vanishing sections over
every open contained in it.

The basic opens of an affine open form a basis of its topology, the sections there vanish by
localization, and vanishing of a section is a local condition. -/
theorem submodule_obj_eq_bot_of_le_affine {M : X.Modules} [M.IsQuasicoherent] (P : M.Submodule)
    (hP : P.toSheafOfModules.IsQuasicoherent) {W : X.Opens} (hW : IsAffineOpen W)
    (hPW : P.toSubmodule.obj (op W) = ⊥) {W₀ : X.Opens} (hW₀ : W₀ ≤ W) :
    P.toSubmodule.obj (op W₀) = ⊥ := by
  refine le_antisymm (fun s hs => ?_) bot_le
  have hmem : s ∈ (Stacks.Algebraization.kernelSubmodule (𝟙 M)).toSubmodule.obj (op W₀) := by
    refine (Stacks.Algebraization.kernelSubmodule (𝟙 M)).isSheaf s fun x hx => ?_
    obtain ⟨g, hgle, hxg⟩ := hW.exists_basicOpen_le (V := W₀) ⟨x, hx⟩ (hW₀ hx)
    refine ⟨X.basicOpen g, CategoryTheory.homOfLE hgle, ?_, hxg⟩
    have h2 : M.val.map (CategoryTheory.homOfLE hgle).op s ∈
        P.toSubmodule.obj (op (X.basicOpen g)) := val_map_mem_submodule P _ hs
    rw [submodule_obj_basicOpen_eq_bot P hP hW hPW g] at h2
    show M.val.map (CategoryTheory.homOfLE hgle).op s ∈
      (Stacks.Algebraization.kernelSubmodule (𝟙 M)).toSubmodule.obj (op (X.basicOpen g))
    rw [kernelSubmodule_id_obj]
    exact h2
  rw [kernelSubmodule_id_obj] at hmem
  exact hmem

end AlgebraicGeometry

namespace SheafOfModules.Submodule

open AlgebraicGeometry

variable {X : Scheme.{u}} {M : X.Modules}

/-! ### The comap of a submodule along an open -/

open AlgebraicGeometry (val_map_congr val_map_map val_map_id val_map_mem_submodule)

/-- The sections of `M` whose restriction to `V` lies in `K`, as a family of submodules stable
under restriction. -/
def comapOpenToSubmodule (K : M.Submodule) (V : X.Opens) : M.val.Submodule where
  obj W := (K.toSubmodule.obj (op (W.unop ⊓ V))).comap
    (M.val.restrictₛₗ (CategoryTheory.homOfLE (inf_le_left : W.unop ⊓ V ≤ W.unop)).op)
  map {W W'} f s hs := by
    simp only [_root_.Submodule.mem_comap, PresheafOfModules.restrictₛₗ_apply] at hs
    change M.val.map (CategoryTheory.homOfLE (inf_le_left : W'.unop ⊓ V ≤ W'.unop)).op
      (M.val.map f s) ∈ K.toSubmodule.obj (op (W'.unop ⊓ V))
    have htr : W'.unop ⊓ V ≤ W.unop := inf_le_left.trans (leOfHom f.unop)
    have h := val_map_mem_submodule K
      (CategoryTheory.homOfLE
        (inf_le_inf_right V (leOfHom f.unop) : W'.unop ⊓ V ≤ W.unop ⊓ V)).op hs
    rw [val_map_map _ _ s (CategoryTheory.homOfLE htr).op] at h
    rw [val_map_map f _ s (CategoryTheory.homOfLE htr).op]
    exact h

/-- The sections of `M` whose restriction to `V` lies in `K`. This is the largest submodule of `M`
agreeing with `K` over `V`. -/
def comapOpen (K : M.Submodule) (V : X.Opens) : M.Submodule where
  toSubmodule := comapOpenToSubmodule K V
  isSheaf {W} s hs := by
    change M.val.map (CategoryTheory.homOfLE (inf_le_left : W.unop ⊓ V ≤ W.unop)).op s ∈
      K.toSubmodule.obj (op (W.unop ⊓ V))
    refine K.isSheaf _ fun x hx => ?_
    obtain ⟨W₀, f, hf, hxW₀⟩ := hs x hx.1
    refine ⟨W₀ ⊓ V, CategoryTheory.homOfLE (inf_le_inf_right V (leOfHom f)), ?_, hxW₀, hx.2⟩
    have htr : W₀ ⊓ V ≤ W.unop := inf_le_left.trans (leOfHom f)
    have hf' : M.val.map (CategoryTheory.homOfLE (inf_le_left : W₀ ⊓ V ≤ W₀)).op
        (M.val.map f.op s) ∈ K.toSubmodule.obj (op (W₀ ⊓ V)) := hf
    rw [val_map_map f.op _ s (CategoryTheory.homOfLE htr).op] at hf'
    change M.val.map (CategoryTheory.homOfLE (inf_le_inf_right V (leOfHom f))).op
      (M.val.map (CategoryTheory.homOfLE (inf_le_left : W.unop ⊓ V ≤ W.unop)).op s) ∈
        K.toSubmodule.obj (op (W₀ ⊓ V))
    rw [val_map_map _ _ s (CategoryTheory.homOfLE htr).op]
    exact hf'

/-- A section lies in `K.comapOpen V` exactly when its restriction to `V` lies in `K`. -/
theorem mem_comapOpen_iff (K : M.Submodule) (V W : X.Opens) (s : Γ(M, W)) :
    s ∈ (comapOpen K V).toSubmodule.obj (op W) ↔
      M.val.map (CategoryTheory.homOfLE (inf_le_left : W ⊓ V ≤ W)).op s ∈
        K.toSubmodule.obj (op (W ⊓ V)) :=
  Iff.rfl

/-- `K` is contained in `comapOpen K V`. -/
theorem le_comapOpen (K : M.Submodule) (V : X.Opens) : K ≤ comapOpen K V :=
  fun _ _ hs ↦ val_map_mem_submodule K _ hs

/-- The comap of `K` along `V` agrees with `K` over `V`. -/
theorem comapOpen_obj_of_le (K : M.Submodule) {V W : X.Opens} (hW : W ≤ V) :
    (comapOpen K V).toSubmodule.obj (op W) = K.toSubmodule.obj (op W) := by
  refine le_antisymm (fun s hs => ?_) (le_comapOpen K V (op W))
  have h : M.val.map (CategoryTheory.homOfLE (inf_le_left : W ⊓ V ≤ W)).op s ∈
    K.toSubmodule.obj (op (W ⊓ V)) := hs
  have h2 := val_map_mem_submodule K
    (CategoryTheory.homOfLE (le_inf (le_refl W) hW : W ≤ W ⊓ V)).op h
  rw [val_map_map _ _ s (𝟙 (op W)), val_map_id] at h2
  exact h2

/-- Membership in a comap along `V` is decided over any open containing `V`: a section whose
restriction to an open `V'` containing `V` lies in `K.comapOpen V` lies in it already. -/
theorem mem_comapOpen_of_mem_inf (K : M.Submodule) {V V' W : X.Opens} (hV : V ≤ V')
    {s : Γ(M, W)}
    (hs : M.val.map (CategoryTheory.homOfLE (inf_le_left : W ⊓ V' ≤ W)).op s ∈
      (comapOpen K V).toSubmodule.obj (op (W ⊓ V'))) :
    s ∈ (comapOpen K V).toSubmodule.obj (op W) := by
  have htr : W ⊓ V' ⊓ V ≤ W := inf_le_left.trans inf_le_left
  have h : M.val.map
      (CategoryTheory.homOfLE (inf_le_left : W ⊓ V' ⊓ V ≤ W ⊓ V')).op
      (M.val.map (CategoryTheory.homOfLE (inf_le_left : W ⊓ V' ≤ W)).op s) ∈
        K.toSubmodule.obj (op (W ⊓ V' ⊓ V)) := hs
  rw [val_map_map _ _ s (CategoryTheory.homOfLE htr).op] at h
  have hle : W ⊓ V ≤ W ⊓ V' ⊓ V :=
    le_inf (le_inf inf_le_left (inf_le_right.trans hV)) inf_le_right
  have h2 := val_map_mem_submodule K (CategoryTheory.homOfLE hle).op h
  rw [val_map_map _ _ s (CategoryTheory.homOfLE (inf_le_left : W ⊓ V ≤ W)).op] at h2
  show M.val.map (CategoryTheory.homOfLE (inf_le_left : W ⊓ V ≤ W)).op s ∈
    K.toSubmodule.obj (op (W ⊓ V))
  exact h2

end SheafOfModules.Submodule

namespace AlgebraicGeometry

attribute [local instance_reducible] AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-! ### Quasi-coherence over a union of opens -/

/-- The inclusion of one submodule of an `𝒪_X`-module into a larger one, typed at `X.Modules`. -/
def submoduleHomOfLE {M : X.Modules} {N₁ N₂ : M.Submodule} (h : N₁ ≤ N₂) :
    Scheme.Modules.Hom (N₁.toSheafOfModules : X.Modules) (N₂.toSheafOfModules : X.Modules) :=
  SheafOfModules.Submodule.homOfLE h

/-- Over an open on which two nested submodules have the same sections, their inclusion is
bijective on sections. -/
theorem isIso_submoduleHomOfLE_app {M : X.Modules} {N₁ N₂ : M.Submodule} (h : N₁ ≤ N₂)
    (W : X.Opens) (hW : N₂.toSubmodule.obj (op W) ≤ N₁.toSubmodule.obj (op W)) :
    IsIso ((submoduleHomOfLE h).app W) := by
  refine (ConcreteCategory.isIso_iff_bijective _).2
    ⟨fun a b hab => ?_, fun y => ⟨⟨y.1, hW y.2⟩, rfl⟩⟩
  have h2 := congrArg Subtype.val hab
  exact Subtype.ext h2

/-- A morphism which is bijective on sections over every open contained in `V` becomes invertible
after restriction along an open immersion whose image lies in `V`. -/
theorem isIso_restrictFunctor_map_of_range_le {Z : Scheme.{u}} {M N : X.Modules} (g : M ⟶ N)
    (f : Z ⟶ X) [IsOpenImmersion f] {V : X.Opens} (hf : Set.range f.base ⊆ (V : Set X))
    (h : ∀ W : X.Opens, W ≤ V → IsIso (g.app W)) :
    IsIso ((Scheme.Modules.restrictFunctor f).map g) := by
  apply isIso_of_isIso_app
  intro W
  show IsIso (g.app (f ''ᵁ W))
  refine h _ fun x hx => ?_
  obtain ⟨y, -, rfl⟩ := hx
  exact hf ⟨y, rfl⟩

/-- The inclusion of one submodule in another becomes invertible after restriction along an open
immersion whose image lies in an open on which they have the same sections. -/
private theorem isIso_restrictFunctor_map_submoduleHomOfLE_of_range_le {Z : Scheme.{u}}
    {M : X.Modules} {L A : M.Submodule} (hle : L ≤ A) {V : X.Opens}
    (hagree : ∀ W : X.Opens, W ≤ V → A.toSubmodule.obj (op W) ≤ L.toSubmodule.obj (op W))
    (f : Z ⟶ X) [IsOpenImmersion f] (hf : Set.range f.base ⊆ (V : Set X)) :
    IsIso ((Scheme.Modules.restrictFunctor f).map (submoduleHomOfLE hle)) :=
  isIso_restrictFunctor_map_of_range_le _ f hf
    fun W hW => isIso_submoduleHomOfLE_app hle W (hagree W hW)

/-- The inclusion of one submodule in another becomes invertible after restriction to an open on
which they have the same sections. -/
theorem isIso_restrictFunctor_map_submoduleHomOfLE {M : X.Modules} {L A : M.Submodule}
    (hle : L ≤ A) (V : X.Opens)
    (hagree : ∀ W : X.Opens, W ≤ V → A.toSubmodule.obj (op W) ≤ L.toSubmodule.obj (op W)) :
    IsIso ((Scheme.Modules.restrictFunctor V.ι).map (submoduleHomOfLE hle)) :=
  isIso_restrictFunctor_map_submoduleHomOfLE_of_range_le hle hagree V.ι (le_of_eq V.range_ι)

/-- Over an open on which two nested submodules have the same sections, the larger is
quasi-coherent as soon as the smaller is. -/
theorem isQuasicoherent_restrict_of_le_of_agree {M : X.Modules} {L A : M.Submodule}
    (hle : L ≤ A) {V : X.Opens}
    (hagree : ∀ W : X.Opens, W ≤ V → A.toSubmodule.obj (op W) ≤ L.toSubmodule.obj (op W))
    (hL : ((Scheme.Modules.restrictFunctor V.ι).obj
      (L.toSheafOfModules : X.Modules)).IsQuasicoherent) :
    ((Scheme.Modules.restrictFunctor V.ι).obj
      (A.toSheafOfModules : X.Modules)).IsQuasicoherent :=
  have hiso := isIso_restrictFunctor_map_submoduleHomOfLE hle V hagree
  (SheafOfModules.isQuasicoherent V.toScheme.ringCatSheaf).prop_of_iso
    (@asIso V.toScheme.Modules _ _ _ _ hiso) hL

/-- Restriction of a quasi-coherent module along an open immersion whose image lies in `V`, where
the module is a submodule agreeing over `V` with a submodule quasi-coherent there, is
quasi-coherent. -/
private theorem isQuasicoherent_restrict_of_agree {M : X.Modules} {L A : M.Submodule}
    (hle : L ≤ A) {V : X.Opens}
    (hagree : ∀ W : X.Opens, W ≤ V → A.toSubmodule.obj (op W) ≤ L.toSubmodule.obj (op W))
    (hA : ((Scheme.Modules.restrictFunctor V.ι).obj
      (A.toSheafOfModules : X.Modules)).IsQuasicoherent)
    {Z : Scheme.{u}} (f : Z ⟶ X) [IsOpenImmersion f] (hf : Set.range f.base ⊆ (V : Set X)) :
    ((Scheme.Modules.restrictFunctor f).obj
      (L.toSheafOfModules : X.Modules)).IsQuasicoherent := by
  have hiso := isIso_restrictFunctor_map_submoduleHomOfLE_of_range_le hle hagree f hf
  -- factor `f` through `V.ι`
  have hran : Set.range f.base ⊆ Set.range V.ι.base := by
    rw [Scheme.Opens.range_ι]; exact hf
  have hfac : f = IsOpenImmersion.lift V.ι f hran ≫ V.ι :=
    (IsOpenImmersion.lift_fac V.ι f hran).symm
  have hAf : ((Scheme.Modules.restrictFunctor f).obj
      (A.toSheafOfModules : X.Modules)).IsQuasicoherent := by
    have _hA := hA
    refine (SheafOfModules.isQuasicoherent Z.ringCatSheaf).prop_of_iso
      (((Scheme.Modules.restrictFunctorCongr hfac).app (A.toSheafOfModules : X.Modules)) ≪≫
        ((Scheme.Modules.restrictFunctorComp (IsOpenImmersion.lift V.ι f hran) V.ι).app
          (A.toSheafOfModules : X.Modules))).symm ?_
    exact Scheme.Modules.isQuasicoherent_restrictFunctor (IsOpenImmersion.lift V.ι f hran) _
  exact (SheafOfModules.isQuasicoherent Z.ringCatSheaf).prop_of_iso
    (@asIso Z.Modules _ _ _ _ hiso).symm hAf

/-- **Quasi-coherence of a glued submodule.** A submodule `L` of a module on a scheme which, over
each member of a family of opens, is contained in and agrees with a submodule quasi-coherent
there, is quasi-coherent over the union of the family.

The union is covered by its members, and over each of them `L` is isomorphic to the submodule it
agrees with there, so the criterion that quasi-coherence is local on the base applies. -/
theorem isQuasicoherent_restrict_iSup_of_agree {M : X.Modules} (L : M.Submodule) {I : Type w}
    (V : I → X.Opens) (A : I → M.Submodule) (hle : ∀ i, L ≤ A i)
    (hagree : ∀ (i : I) (W : X.Opens), W ≤ V i →
      (A i).toSubmodule.obj (op W) ≤ L.toSubmodule.obj (op W))
    (hA : ∀ i, ((Scheme.Modules.restrictFunctor (V i).ι).obj
      ((A i).toSheafOfModules : X.Modules)).IsQuasicoherent) :
    ((Scheme.Modules.restrictFunctor (⨆ i, V i).ι).obj
      (L.toSheafOfModules : X.Modules)).IsQuasicoherent := by
  set S : X.Opens := ⨆ i, V i with hS
  refine Stacks.Modules.isQuasicoherent_of_restrict _ (fun i => S.ι ⁻¹ᵁ V i) ?_ fun i => ?_
  · rw [← Scheme.Hom.preimage_iSup, ← hS, Scheme.Opens.ι_preimage_self]
  · have hran : Set.range ((S.ι ⁻¹ᵁ V i).ι ≫ S.ι).base ⊆ (V i : Set X) := by
      intro x hx
      obtain ⟨y, rfl⟩ := hx
      exact y.2
    refine (SheafOfModules.isQuasicoherent (S.ι ⁻¹ᵁ V i).toScheme.ringCatSheaf).prop_of_iso
      ((Scheme.Modules.restrictFunctorComp (S.ι ⁻¹ᵁ V i).ι S.ι).app
        (L.toSheafOfModules : X.Modules)) ?_
    exact isQuasicoherent_restrict_of_agree (hle i) (hagree i) (hA i)
      ((S.ι ⁻¹ᵁ V i).ι ≫ S.ι) hran

end AlgebraicGeometry

end
