module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CoherenceClosure
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleSummandNoSliceSheafify
public import StacksFrontier.AlgebraicGeometry.CoherenceCriteria.Affine
public import StacksFrontier.AlgebraicGeometry.Cohomology.Coherent.FiniteTilde
public import StacksFrontier.AlgebraicGeometry.AffineQcohPushforward.Basic
public import StacksFrontier.Topology.Sheaves.Modules.LocallyFree
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleSummandSheafify
public import Mathlib.Data.List.TFAE
public import StacksCore.Tactic.StacksAttribute

@[expose] public section

open CategoryTheory Limits SheafOfModules TopologicalSpace
open AlgebraicGeometry
open Stacks.AlgebraicGeometry.CoherentTFAE

universe v₂ u₂ u

namespace Stacks.AlgebraicGeometry.CoherenceCriteria

/-! ### The kernel clause at one open, and its locality -/

section RingedSpace

variable {X : Type u} [TopologicalSpace X]
  {R : Sheaf (Opens.grothendieckTopology X) RingCat.{u}}

/-- **The kernel clause of coherence at one open.** Over the open `W`, the kernel of every
morphism into `M|_W` from a sheaf of modules with finitely many generating sections is of finite
type. This is condition (2) of [Stacks, Tag 01BV] localized at `W`, in the form in which
`Stacks.SheafOfModules.isFiniteType_kernel_over_aux` consumes it. -/
def KernelClause (M : SheafOfModules.{u} R) (W : Opens X) : Prop :=
  ∀ (N : SheafOfModules.{u} (R.over W)) (σ : N.GeneratingSections), Finite σ.I →
    ∀ g : N ⟶ M.over W, (kernel g).IsFiniteType

/-- The kernel clause at `Z.left` computes the kernel of a morphism out of a finite free module
over the slice site at `U`, restricted to `Z`.

This is the body of `Stacks.SheafOfModules.isFiniteType_kernel_over_aux` run against
`KernelClause` instead of against coherence of the ambient sheaf: the restriction of `φ` to `Z`
is carried along `Stacks.SheafOfModules.overOverEquivalence` to a morphism into `M|_{Z.left}`,
where the hypothesis applies, and carried back along
`CategoryTheory.Limits.PreservesKernel.iso` and `Stacks.SheafOfModules.overKernelIso`. -/
theorem isFiniteType_kernel_over_of_kernelClause {M : SheafOfModules.{u} R}
    (U : Opens X) {A : Type u} [Finite A]
    (φ : (free A : SheafOfModules.{u} (R.over U)) ⟶ M.over U) (Z : Over U)
    (hcl : KernelClause M Z.left) : ((kernel φ).over Z).IsFiniteType := by
  have key : (kernel (φ.over Z)).IsFiniteType := by
    let e := Stacks.SheafOfModules.overOverEquivalence (R := R) U Z
    let τ : ((free A : SheafOfModules.{u} (R.over U)).over Z).GeneratingSections :=
      (free.generatingSections (R := R.over U) A).map (overFunctor (R.over U) Z) (by rfl)
    let σ := τ.map e.inverse (Iso.refl (unit (R.over Z.left)))
    have hfin : Finite σ.I := inferInstanceAs (Finite A)
    have h2 := hcl _ σ hfin
      (e.inverse.map (φ.over Z) ≫ (Stacks.SheafOfModules.overOverIso M U Z).hom)
    have h3 : (kernel (e.inverse.map (φ.over Z))).IsFiniteType :=
      Stacks.SheafOfModules.isFiniteType_of_iso.{u}
        (M := kernel (e.inverse.map (φ.over Z) ≫
          (Stacks.SheafOfModules.overOverIso M U Z).hom))
        (N := kernel (e.inverse.map (φ.over Z)))
        (kernel.mapIso _ (e.inverse.map (φ.over Z))
          (Iso.refl _) (Stacks.SheafOfModules.overOverIso M U Z).symm (by simp))
    have h4 : (e.inverse.obj (kernel (φ.over Z))).IsFiniteType :=
      Stacks.SheafOfModules.isFiniteType_of_iso.{u}
        (PreservesKernel.iso e.inverse (φ.over Z)).symm
    exact Stacks.SheafOfModules.isFiniteType_of_overOverEquivalence_inverse U Z h4
  exact Stacks.SheafOfModules.isFiniteType_of_iso.{u}
    (Stacks.SheafOfModules.overKernelIso φ Z).symm

end RingedSpace

/-! ### The affine opens below an open cover its slice site -/

/-- **The affine opens contained in `W` cover the slice site at `W`.** Affine opens form a basis
of the topology of a scheme, so every object of `Over W` is covered by the affine opens below
it, and those are themselves objects of `Over W`. -/
theorem coversTop_affineOpens_over {X : Scheme.{u}} (W : X.Opens) :
    ((Opens.grothendieckTopology ↥X).over W).CoversTop
      (fun V : {V : X.Opens // IsAffineOpen V ∧ V ≤ W} =>
        (Over.mk (homOfLE V.2.2) : Over W)) := by
  intro Y
  rw [GrothendieckTopology.mem_over_iff, Opens.mem_grothendieckTopology]
  intro x hx
  obtain ⟨T, hT, hxT, hTY⟩ := Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens hx
  refine ⟨T, homOfLE hTY, ?_, hxT⟩
  rw [Sieve.overEquiv_iff]
  exact (Sieve.mem_ofObjects_iff _ _).2
    ⟨⟨T, hT, hTY.trans (leOfHom Y.hom)⟩, ⟨Over.homMk (homOfLE le_rfl)⟩⟩

/-! ### The kernel clause on a locally Noetherian scheme -/

/-- **The kernel clause holds at every affine open.** This is the affine Noetherian input of
[Stacks, Tag 01XZ]: a morphism from a sheaf of modules with finitely many generating sections is
reduced to one out of a finite free module, and there the kernel's sections over the affine open
are a submodule of a finite module over a Noetherian ring. -/
theorem kernelClause_of_isAffineOpen {X : Scheme.{u}} [IsLocallyNoetherian X]
    (F : X.Modules) [F.IsQuasicoherent] {V : X.Opens} (hV : IsAffineOpen V) :
    KernelClause F V := by
  intro N σ hσ g
  have := hσ
  obtain ⟨ρ, hρ⟩ := exists_finite_generatingSections_kernel_of_isAffineOpen F hV (σ.π ≫ g)
  have hbp : HasBinaryProducts (Over V) :=
    CategoryTheory.Over.ConstructProducts.over_binaryProduct_of_pullback
  have hρ' : ρ.IsFiniteType := ⟨hρ⟩
  have h1 : (kernel (σ.π ≫ g)).IsFiniteType :=
    Stacks.SheafOfModules.isFiniteType_of_generatingSections.{u} ρ
  exact Stacks.SheafOfModules.isFiniteType_kernel_of_epi_comp σ.π g h1

/-- **(2) ⇒ (1) of [Stacks, Tag 01XZ].** On a locally Noetherian scheme a quasi-coherent module
of finite type is coherent.

The kernel condition of `Stacks.SheafOfModules.IsCoherent` is checked over the affine opens
below the given open, which cover its slice site, and there it is the statement that a submodule
of a finite module over a Noetherian ring is finitely generated. -/
theorem isCoherent_of_isQuasicoherent_of_isFiniteType {X : Scheme.{u}} [IsLocallyNoetherian X]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] :
    F.IsCoherent where
  isFiniteType := inferInstance
  kernel_isFiniteType U A hA φ := by
    have := hA
    exact Stacks.SheafOfModules.LocalKernel.isFiniteType_of_coversTop (kernel φ)
      (fun V : {V : X.Opens // IsAffineOpen V ∧ V ≤ U} => (Over.mk (homOfLE V.2.2) : Over U))
      (coversTop_affineOpens_over U)
      fun V => isFiniteType_kernel_over_of_kernelClause U φ _
        (kernelClause_of_isAffineOpen F V.2.1)

/-! ### The remaining implications into coherence -/

/-- A quasi-coherent module of finite type, given as a conjunction, is coherent. -/
private theorem isCoherent_of_and {X : Scheme.{u}} [IsLocallyNoetherian X] (F : X.Modules)
    (h : F.IsQuasicoherent ∧ F.IsFiniteType) : F.IsCoherent :=
  have := h.1
  have := h.2
  isCoherent_of_isQuasicoherent_of_isFiniteType F

/-- **(3) ⇒ (1) of [Stacks, Tag 01XZ].** On a locally Noetherian scheme a module of finite
presentation is coherent. -/
theorem isCoherent_of_isFinitePresentation {X : Scheme.{u}} [IsLocallyNoetherian X]
    (F : X.Modules) (h : F.IsFinitePresentation) : F.IsCoherent :=
  isCoherent_of_and F (isQuasicoherent_isFiniteType_of_isFinitePresentation F h)

/-- **(4) ⇒ (1) of [Stacks, Tag 01XZ].** On a locally Noetherian scheme a module which on every
affine open is the sheaf associated with a finite module is coherent. -/
theorem isCoherent_of_isFiniteTildeOn {X : Scheme.{u}} [IsLocallyNoetherian X] (F : X.Modules)
    (h : ∀ (U : X.Opens) (hU : IsAffineOpen U), IsFiniteTildeOn F U hU) :
    F.IsCoherent :=
  isCoherent_of_and F (isQuasicoherent_isFiniteType_of_cover_isFiniteTildeOn F
    (exists_affineOpenCover_isFiniteTildeOn F h))

/-- **(5) ⇒ (1) of [Stacks, Tag 01XZ].** On a locally Noetherian scheme a module which on the
members of some affine open covering is the sheaf associated with a finite module is coherent. -/
theorem isCoherent_of_exists_affineOpenCover_isFiniteTildeOn {X : Scheme.{u}}
    [IsLocallyNoetherian X] (F : X.Modules)
    (h : ∃ (ι : Type u) (U : ι → X.Opens), IsOpenCover U ∧
      ∀ i, ∃ hU : IsAffineOpen (U i), IsFiniteTildeOn F (U i) hU) :
    F.IsCoherent :=
  isCoherent_of_and F (isQuasicoherent_isFiniteType_of_cover_isFiniteTildeOn F h)

/-! ### The five equivalent conditions -/

/-- **[Stacks, Tag 01XZ].** On a locally Noetherian scheme the following are equivalent for a
module `F`: it is coherent; it is quasi-coherent and of finite type; it is of finite
presentation; on every affine open it is the sheaf associated with a finite module; on the
members of some affine open covering it is the sheaf associated with a finite module. -/
@[stacks 01XZ "five equivalent conditions", ega "I 1.5.1" "(a) <=> (b)"]
theorem coherent_tfae (X : Scheme.{u}) [IsLocallyNoetherian X] (F : X.Modules) :
    List.TFAE [
      F.IsCoherent,
      F.IsQuasicoherent ∧ F.IsFiniteType,
      F.IsFinitePresentation,
      ∀ (U : X.Opens) (hU : IsAffineOpen U), IsFiniteTildeOn F U hU,
      ∃ (ι : Type u) (U : ι → X.Opens),
        IsOpenCover U ∧ ∀ i, ∃ hU : IsAffineOpen (U i), IsFiniteTildeOn F (U i) hU] := by
  tfae_have 1 → 2 := fun h =>
    have := h
    isQuasicoherent_isFiniteType_of_isCoherent F
  tfae_have 2 → 1 := isCoherent_of_and F
  tfae_have 1 → 3 := fun h =>
    have := h
    isFinitePresentation_of_isCoherent' F
  tfae_have 3 → 2 := fun h => isQuasicoherent_isFiniteType_of_isFinitePresentation F h
  tfae_have 2 → 4 := fun h U hU =>
    have := h.1
    have := h.2
    isFiniteTildeOn_of_isQuasicoherent_of_isFiniteType F U hU
  tfae_have 4 → 5 := fun h => exists_affineOpenCover_isFiniteTildeOn F h
  tfae_have 5 → 2 := fun h => isQuasicoherent_isFiniteType_of_cover_isFiniteTildeOn F h
  tfae_finish

/-! ### The structure sheaf -/

section Unit

variable {C : Type u} [Category.{u, u} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}}
  [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **The identity section generates the unit sheaf of modules.** The associated map
`free PUnit ⟶ unit R` is split by the inclusion of the single summand. -/
noncomputable def unitGeneratingSections : (unit R).GeneratingSections where
  I := PUnit.{u + 1}
  s _ := (unit R).unitHomEquiv (𝟙 _)
  epi := by
    have h : ιFree (R := R) (PUnit.unit : PUnit.{u + 1}) ≫
        (unit R).freeHomEquiv.symm (fun _ : PUnit.{u + 1} => (unit R).unitHomEquiv (𝟙 _)) =
        𝟙 _ := by
      rw [← unitHomEquiv_symm_freeHomEquiv_apply]
      simp
    have : IsSplitEpi ((unit R).freeHomEquiv.symm
        (fun _ : PUnit.{u + 1} => (unit R).unitHomEquiv (𝟙 _))) := ⟨⟨_, h⟩⟩
    infer_instance

instance unitGeneratingSections_isFiniteType :
    (unitGeneratingSections (R := R)).IsFiniteType where
  finite := inferInstanceAs (Finite PUnit.{u + 1})

end Unit

/-- **The structure sheaf of a scheme is of finite type**, being generated by the single
section `1`. -/
instance isFiniteType_unit (X : Scheme.{u}) :
    (SheafOfModules.unit X.ringCatSheaf).IsFiniteType :=
  Stacks.SheafOfModules.isFiniteType_of_generatingSections.{u} unitGeneratingSections

/-- **[Stacks, Tag 01XZ].** The structure sheaf of a locally Noetherian scheme is coherent. -/
@[instance, stacks 01XZ "the structure sheaf is coherent"]
theorem structureSheaf_isCoherent (X : Scheme.{u}) [IsLocallyNoetherian X] :
    (SheafOfModules.unit X.ringCatSheaf).IsCoherent :=
  isCoherent_of_isQuasicoherent_of_isFiniteType _

/-! ### Finite locally free modules -/

section LocallyFree

variable {C : Type u} [Category.{u, u} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  [∀ Y, HasWeakSheafify (J.over Y) AddCommGrpCat.{u}]
  [∀ Y, (J.over Y).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- A finite locally free sheaf of modules is of finite type: its locally free data is already
local generators data with finite generating families. -/
theorem isFiniteType_of_isFiniteLocallyFree (M : SheafOfModules.{u} R)
    [h : _root_.AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree M] : M.IsFiniteType := by
  obtain ⟨q, -, hq⟩ := h.exists_isFiniteLocallyFreeData
  exact ⟨q, hq⟩

/-- A finite locally free sheaf of modules is quasi-coherent, being locally free. -/
theorem isQuasicoherent_of_isFiniteLocallyFree (M : SheafOfModules.{u} R)
    [_root_.AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree M] : M.IsQuasicoherent :=
  have : M.IsLocallyFree := inferInstance
  inferInstance

end LocallyFree

/-- **[Stacks, Tag 01XZ].** A finite locally free module on a locally Noetherian scheme is
coherent. -/
@[instance, stacks 01XZ "finite locally free modules are coherent"]
theorem isCoherent_of_isFiniteLocallyFree (X : Scheme.{u}) [IsLocallyNoetherian X]
    (F : X.Modules) [_root_.AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree
      (C := Opens ↥X) (J := Opens.grothendieckTopology ↥X) F] : F.IsCoherent :=
  @isCoherent_of_isQuasicoherent_of_isFiniteType X _ F
    (isQuasicoherent_of_isFiniteLocallyFree F) (isFiniteType_of_isFiniteLocallyFree F)

/-! ### Invertible modules -/

/-- **A split monomorphism exhibits its source as the kernel of `1 - e`**, where `e` is the
associated split idempotent. -/
noncomputable def isoKernelOneSubSplitIdempotent {D : Type u₂} [Category.{v₂} D] [Preadditive D]
    {M P : D} (s : M ⟶ P) [IsSplitMono s] [HasKernel (𝟙 P - retraction s ≫ s)] :
    M ≅ kernel (𝟙 P - retraction s ≫ s) where
  hom := kernel.lift _ s (by
    rw [Preadditive.comp_sub, Category.comp_id, ← Category.assoc, IsSplitMono.id,
      Category.id_comp, sub_self])
  inv := kernel.ι _ ≫ retraction s
  hom_inv_id := by rw [← Category.assoc, kernel.lift_ι, IsSplitMono.id]
  inv_hom_id := by
    refine (cancel_mono (kernel.ι (𝟙 P - retraction s ≫ s))).1 ?_
    have h : kernel.ι (𝟙 P - retraction s ≫ s) ≫ (𝟙 P - retraction s ≫ s) = 0 :=
      kernel.condition _
    rw [Preadditive.comp_sub, Category.comp_id, sub_eq_zero] at h
    rw [Category.assoc, kernel.lift_ι, Category.id_comp, Category.assoc]
    exact h.symm

/-- The root coherence class from the `Stacks` one: `Stacks.SheafOfModules.IsCoherent F` implies
`SheafOfModules.IsCoherent F`.

**These are two different constants, and this theorem is a bridge between them.**
`SheafOfModules.IsCoherent` is declared at
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/CoherentFinitePresentation.lean`, and
`Stacks.SheafOfModules.IsCoherent` at
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/Coherent.lean`. They have the same two fields, so
`⟨h.1, h.2⟩` crosses between them, and their pretty-printed forms differ only by a namespace that
`open AlgebraicGeometry`-style preludes usually hide — which is exactly why the gap is easy to
miss. `#check` with `set_option pp.fullNames true` distinguishes them; nothing else reliably
does.

Of the 357 consumer declarations across 111 modules, **317 state the root class and 40 the
`Stacks` one**, and 18 of those 40 are the three files that develop the theory. So the theory is
built at the `Stacks` class and consumed at the root one, and this bridge is the usual direction
of travel. `infer_instance` crosses **neither** way, so every crossing is a deliberate
application of this theorem or of one of its siblings in
`LocalCohomology/ImprovingCoherentModules/KernelCokernel.lean`,
`StacksFrontier/AlgebraicGeometry/TensorCoherence/Basic.lean` or
`StacksFrontier/AlgebraicGeometry/ReflexiveHull/CoherentReflexive.lean`.

In particular `Stacks.SheafOfModules.IsCoherent` is *not* the only coherence class in the library,
and the gap between the two is not a transparency mismatch at `X.ringCatSheaf`. A module whose
theorem is phrased at the wrong one of these two compiles, has a clean `#print axioms`, and proves
the neighbouring statement. -/
theorem isCoherent_of_isCoherent' {X : Scheme.{u}} {F : X.Modules}
    (h : Stacks.SheafOfModules.IsCoherent F) : F.IsCoherent := ⟨h.1, h.2⟩

/-- The converse spelling change of `isCoherent_of_isCoherent'`. -/
theorem isCoherent'_of_isCoherent {X : Scheme.{u}} {F : X.Modules}
    (h : F.IsCoherent) : Stacks.SheafOfModules.IsCoherent F := ⟨h.1, h.2⟩

/-- **[Stacks, Tag 01XZ].** An invertible module on a locally Noetherian scheme is coherent.

By [Stacks, Tag 0B8N] (b) an invertible module is, on a covering of the whole scheme, a direct
summand of a finite free module, hence the kernel of `1 - e` for the associated split idempotent;
and the structure sheaf is coherent, so
`Stacks.SheafOfModules.isCoherent_of_locallyKernelFiniteCoproduct` applies. -/
@[instance, stacks 01XZ "invertible modules are coherent"]
theorem isCoherent_of_isInvertible (X : Scheme.{u}) [IsLocallyNoetherian X] (F : X.Modules)
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property F] :
    F.IsCoherent := by
  have hG : Stacks.SheafOfModules.IsCoherent (SheafOfModules.unit X.ringCatSheaf) :=
    isCoherent'_of_isCoherent (structureSheaf_isCoherent X)
  refine isCoherent_of_isCoherent' ?_
  refine @Stacks.SheafOfModules.isCoherent_of_locallyKernelFiniteCoproduct ↥X _
    X.ringCatSheaf F (SheafOfModules.unit X.ringCatSheaf) hG ?_
  intro x
  obtain ⟨I, V, f, hcov, hsum⟩ :=
    Stacks.SheafOfModules.exists_cover_isDirectSummand_finiteFree
      (O := X.sheaf.obj) X.ringCatSheaf.property F ⊤
  obtain ⟨W, g, hgS, hxW⟩ := (Opens.mem_grothendieckTopology ↥X).mp hcov x (Set.mem_univ x)
  obtain ⟨Z, h, g', hg', -⟩ := hgS
  obtain ⟨i⟩ := hg'
  obtain ⟨n, s, hs⟩ := hsum i
  have hbp : HasFiniteBiproducts (SheafOfModules.{u}
      ((Stacks.SheafOfModules.TensorSheafification.structureSheaf X.sheaf.obj
        X.ringCatSheaf.property).over (V i))) :=
    HasFiniteBiproducts.of_hasFiniteProducts
  have := hs
  let e : (∏ᶜ fun _ : Fin n =>
        unit ((Stacks.SheafOfModules.TensorSheafification.structureSheaf X.sheaf.obj
          X.ringCatSheaf.property).over (V i))) ≅
      (∐ fun _ : Fin n => (SheafOfModules.unit X.ringCatSheaf).over (V i)) :=
    (biproduct.isoProduct _).symm ≪≫ biproduct.isoCoproduct _
  let φ := e.inv ≫ (𝟙 _ - retraction s ≫ s) ≫ e.hom
  refine ⟨V i, (leOfHom h) hxW, n, n, φ, ⟨?_⟩⟩
  refine Iso.trans (isoKernelOneSubSplitIdempotent s) ?_
  exact kernel.mapIso (f := 𝟙 _ - retraction s ≫ s) φ e e (by simp [φ])

end Stacks.AlgebraicGeometry.CoherenceCriteria

namespace AlgebraicGeometry

/-- Over a Noetherian ring, the quasi-coherent sheaf on `Spec R` associated with a finite module
is coherent: it is of finite type by `AlgebraicGeometry.tilde_isFiniteType_iff`, and a
quasi-coherent sheaf of finite type on a locally Noetherian scheme is coherent by
`Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isQuasicoherent_of_isFiniteType`. -/
@[ega "I 1.5.1" "c) ⇒ a), for V = Spec(A)"]
public theorem tilde_isCoherent_of_finite {R : CommRingCat.{u}} [IsNoetherianRing R]
    (M : ModuleCat.{u} R) [Module.Finite R M] : (tilde M).IsCoherent :=
  have : (tilde M).IsFiniteType := (tilde_isFiniteType_iff M).mpr inferInstance
  Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isQuasicoherent_of_isFiniteType
    (tilde M)

end AlgebraicGeometry

end
