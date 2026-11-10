module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.MethodeDeLa.GaloisSubgroupQuotient
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.MethodeDeLa.GaloisCoveringDescentExact
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.MethodeDeLa.ConstantModuleFiltration
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.GaloisTrivializationExists
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.GaloisTrivializationInverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.CoverTriangleModules
public import StacksCore.Tactic.StacksAttribute

/-!
# Filtering a locally constant sheaf of `Λ`-modules after a cover of degree prime to `ℓ`

Let `S` be an irreducible, geometrically unibranch scheme, `ℓ` a prime, `n ≥ 1`, `Λ` a Noetherian
ring and `F` a finite type locally constant sheaf of `Λ`-modules on `S_étale` annihilated by
`ℓ ^ n`. Stacks, Tag 0GJ0 produces a finite étale `f : T ⟶ S` of degree prime to `ℓ` such that
`f⁻¹ F` has a finite filtration with successive quotients the constant sheaves of finite
`Λ`-modules. This file proves it.

## Main results

* `Stacks.EtaleCohomology.exists_finiteEtale_primeToEll_constantModuleFiltration`: Tag 0GJ0.
* `Stacks.EtaleCohomology.exists_finiteEtale_primeToEll_prop_inverseImage`: the same, as an
  induction principle for properties closed under extensions.
* `Stacks.EtaleCohomology.overPullbackIsoConstantOfEtaleModuleInverseImage`: a trivialization of
  `w⁻¹ F` on `W_étale` is a trivialization of `F` on the slice `X_étale / W`.

## The hypotheses on `S`

The geometric unibranch hypothesis is necessary: see the counterexample in the docstring of the
main theorem, the nodal cubic (irreducible, not unibranch) with the coefficient ring `𝔽_ℓ[t, t⁻¹]`.

## References

* [Stacks Project, Tag 0GJ0](https://stacks.math.columbia.edu/tag/0GJ0)
* [Stacks Project, Tag 0GIY](https://stacks.math.columbia.edu/tag/0GIY)
* [Stacks Project, Tag 0GIZ](https://stacks.math.columbia.edu/tag/0GIZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme

universe u r

namespace Stacks.EtaleCohomology

attribute [local instance] moduleCat_hasLimitsOfSize

section Transfer

variable (Λ : Type r) [Ring Λ]

/-- **A trivialization of `w⁻¹ F` on `W_étale` is a trivialization of `F` on the slice
`X_étale / W`**, for the structure morphism `w : W ⟶ X` of an étale `X`-scheme. This is the
converse of `Stacks.EtaleCohomology.etaleModuleInverseImageIsoConstantOfOverPullback`. -/
def overPullbackIsoConstantOfEtaleModuleInverseImage {X : Scheme.{u}} (W : X.Etale)
    (F : EtaleModules.{u, r} Λ X) (M : ModuleCat.{max (u + 1) r} Λ)
    (e : (etaleModuleInverseImage.{u, r} Λ W.hom).obj F ≅
      (constantSheaf W.left.smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ)).obj M) :
    (constantSheaf ((smallEtaleTopology X).over W) (ModuleCat.{max (u + 1) r} Λ)).obj M ≅
      ((smallEtaleTopology X).overPullback _ W).obj F :=
  letI : (Scheme.Etale.smallEtaleCompose W.hom).IsContinuous
      W.left.smallEtaleTopology X.smallEtaleTopology :=
    Scheme.Etale.smallEtaleCompose_isContinuous _
  letI := Functor.isContinuous_comp (etaleLeftOverFunctor W) (Over.forget W)
    W.left.smallEtaleTopology ((smallEtaleTopology X).over W) X.smallEtaleTopology
  let ρ := (etaleLeftOverFunctor W).sheafPushforwardContinuous (ModuleCat.{max (u + 1) r} Λ)
    W.left.smallEtaleTopology ((smallEtaleTopology X).over W)
  let hff : ρ.FullyFaithful := Functor.FullyFaithful.ofFullyFaithful ρ
  hff.preimageIso
    ((Stacks.Cohomology.DenseSubsiteGlobal.constantSheafRestrictionIso
      W.left.smallEtaleTopology ((smallEtaleTopology X).over W) (etaleLeftOverFunctor W)
      (ModuleCat.{max (u + 1) r} Λ)).app M ≪≫ e.symm ≪≫
      (etaleModuleInverseImageRestrictionIso.{u, r} Λ W.hom).app F ≪≫
      (Functor.sheafPushforwardContinuousIso (smallEtaleComposeIsoEtaleLeftOverFunctor W)
        (ModuleCat.{max (u + 1) r} Λ) W.left.smallEtaleTopology X.smallEtaleTopology).app F)

end Transfer

section Quotient

variable {Λ : Type r} [Ring Λ] {S : Scheme.{u}} [IrreducibleSpace S]
  (hS : IsGeometricallyUnibranch S) {x : GeometricPoint S} (A : PointedGaloisCover x)
  (P : Subgroup (Aut A.obj)) [Finite P]

include hS in
/-- **A sheaf trivialized by a pointed Galois cover `A` of `S` has inverse image on `A/P`
trivialized by the Galois covering `A ⟶ A/P`**, with the same value. -/
theorem nonempty_trivialization_galoisSubgroupQuotient (F : EtaleModules.{u, r} Λ S)
    (M : ModuleCat.{max (u + 1) r} Λ) (e : GaloisTrivialization A F M) :
    haveI := A.isGalois
    Nonempty ((constantSheaf ((galoisSubgroupQuotient A.obj P).left.smallEtaleTopology.over
        (galoisSubgroupQuotientCovering A.obj P hS).cover) (ModuleCat.{max (u + 1) r} Λ)).obj M ≅
      ((galoisSubgroupQuotient A.obj P).left.smallEtaleTopology.overPullback _
        (galoisSubgroupQuotientCovering A.obj P hS).cover).obj
          ((etaleModuleInverseImage.{u, r} Λ (galoisSubgroupQuotient A.obj P).hom).obj F)) := by
  have := A.isGalois
  let W := (PointedGaloisCover.toEtale x).obj A
  let π := (galoisSubgroupQuotientπ A.obj P).left
  let Tm := (galoisSubgroupQuotient A.obj P).hom
  have hcomp : π ≫ Tm = W.hom := MorphismProperty.Over.w (galoisSubgroupQuotientπ A.obj P)
  let i1 := etaleModuleInverseImageIsoConstantOfOverPullback W Λ F M e
  let i2 := (etaleModuleInverseImageCompIso.{u, r} Λ π Tm).app F
  let i3 : (etaleModuleInverseImage.{u, r} Λ (π ≫ Tm)).obj F ≅
      (etaleModuleInverseImage.{u, r} Λ W.hom).obj F :=
    eqToIso (congrArg (fun g ↦ (etaleModuleInverseImage.{u, r} Λ g).obj F) hcomp)
  exact ⟨overPullbackIsoConstantOfEtaleModuleInverseImage Λ
    (galoisSubgroupQuotientCovering A.obj P hS).cover _ M (i2.symm ≪≫ i3 ≪≫ i1)⟩

end Quotient

section Transport

/-- The restriction of a representation to a stable submodule. -/
def stableSubmoduleRep {Λ : Type r} [Ring Λ] {P : Type*} [Group P] {N : Type*} [AddCommGroup N]
    [Module Λ N] (ρ : P →* Module.End Λ N) (N₁ : Submodule Λ N)
    (h : ∀ g, ∀ x ∈ N₁, ρ g x ∈ N₁) : P →* Module.End Λ N₁ where
  toFun g := (ρ g).restrict (h g)
  map_one' := by
    ext x
    simp [LinearMap.restrict_apply]
  map_mul' a b := by
    ext x
    simp [LinearMap.restrict_apply, Module.End.mul_apply]

variable {T : Scheme.{u}} {P : Type u} [Group P] (G : EtaleGaloisCovering T P)
  [ConnectedSpace G.cover.left] {Λ : Type r} [CommRing Λ] {N : Type (max (u + 1) r)}
  [AddCommGroup N] [Module Λ N] (ρ : P →* Module.End Λ N) {F' : EtaleModules.{u, r} Λ T}
  (ι : F' ≅ G.descentSheaf Λ N ρ)

/-- The subsheaf of `D(N) ≅ F'` given by a stable submodule `N₁ ⊆ N`: the descent sheaf of `N₁`,
included in `F'`. -/
def descentSubmoduleMap (N₁ : Submodule Λ N) (h : ∀ g, ∀ x ∈ N₁, ρ g x ∈ N₁) :
    G.descentSheaf Λ N₁ (stableSubmoduleRep ρ N₁ h) ⟶ F' :=
  G.descentSheafMap (ρ₁ := stableSubmoduleRep ρ N₁ h) (ρ₂ := ρ) N₁.subtype (fun _ _ ↦ rfl) ≫
    ι.inv

/-- The inclusion of the subsheaf given by a stable submodule is a monomorphism. -/
instance mono_descentSubmoduleMap (N₁ : Submodule Λ N) (h : ∀ g, ∀ x ∈ N₁, ρ g x ∈ N₁) :
    Mono (descentSubmoduleMap G ρ ι N₁ h) :=
  haveI := G.mono_descentSheafMap N₁.subtype (ρ₁ := stableSubmoduleRep ρ N₁ h) (ρ₂ := ρ)
    (fun _ _ ↦ rfl) Subtype.val_injective
  mono_comp _ _

/-- **A step of the filtration of `N` with trivial action on the quotient gives a step of the
filtration of `F'` whose quotient is a constant sheaf of a finite module.** -/
theorem descentSubmoduleMap_mem_constantFiniteModuleStep [IsNoetherianRing Λ]
    [Module.Finite Λ N] {N₁ N₂ : Submodule Λ N} (h₁ : ∀ g, ∀ x ∈ N₁, ρ g x ∈ N₁)
    (h₂ : ∀ g, ∀ x ∈ N₂, ρ g x ∈ N₂) (hle : N₁ ≤ N₂)
    (htriv : ∀ g, ∀ x ∈ N₂, ρ g x - x ∈ N₁) :
    (Subobject.mk (descentSubmoduleMap G ρ ι N₁ h₁),
      Subobject.mk (descentSubmoduleMap G ρ ι N₂ h₂)) ∈ ConstantFiniteModuleStep Λ F' := by
  let K := N₁.comap N₂.subtype
  let Q := ↥N₂ ⧸ K
  let φ := Submodule.inclusion hle
  have hφ : ∀ g x, φ (stableSubmoduleRep ρ N₁ h₁ g x) = stableSubmoduleRep ρ N₂ h₂ g (φ x) :=
    fun _ _ ↦ rfl
  let q := K.mkQ
  have hq : ∀ g x, q (stableSubmoduleRep ρ N₂ h₂ g x) = (1 : P →* Module.End Λ Q) g (q x) := by
    intro g x
    change K.mkQ _ = K.mkQ x
    rw [← sub_eq_zero, ← map_sub, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact htriv g x x.2
  let w := G.descentSheafMap φ hφ
  have hw : w ≫ descentSubmoduleMap G ρ ι N₂ h₂ = descentSubmoduleMap G ρ ι N₁ h₁ := by
    rw [descentSubmoduleMap, descentSubmoduleMap, ← Category.assoc]
    rfl
  obtain ⟨hmk, ⟨iso₁⟩⟩ := exists_cokernel_ofLE_iso_of_comm w hw
  have hS := G.shortExact_descentSheafMap φ hφ q hq (Submodule.inclusion_injective hle)
    K.mkQ_surjective (by rw [Submodule.range_inclusion, Submodule.ker_mkQ])
  let iso₂ : cokernel w ≅ G.descentSheaf Λ Q 1 :=
    (cokernelIsCokernel w).coconePointUniqueUpToIso hS.gIsCokernel
  obtain ⟨iso₃⟩ := G.nonempty_iso_constantSheaf_descentSheaf_one (Λ := Λ) Q
  have hfin₂ : Module.Finite Λ N₂ :=
    Module.Finite.iff_fg.2 (IsNoetherian.noetherian (R := Λ) (M := N) _)
  exact ⟨hmk, ModuleCat.of Λ Q, inferInstanceAs (Module.Finite Λ Q),
    ⟨iso₁ ≪≫ iso₂ ≪≫ iso₃⟩⟩

omit [ConnectedSpace G.cover.left] in
/-- The zero submodule gives the zero subobject. -/
theorem isZero_underlying_descentSubmoduleMap {N₁ : Submodule Λ N}
    (h : ∀ g, ∀ x ∈ N₁, ρ g x ∈ N₁) (hbot : N₁ = ⊥) :
    IsZero (Subobject.underlying.obj (Subobject.mk (descentSubmoduleMap G ρ ι N₁ h))) := by
  have hsub : Subsingleton N₁ := by
    subst hbot
    infer_instance
  have hz : IsZero (G.descentSheaf Λ N₁ (stableSubmoduleRep ρ N₁ h)) := by
    rw [IsZero.iff_id_eq_zero]
    apply Sheaf.hom_ext
    ext W f
    exact Subtype.ext (LocallyConstant.ext fun z ↦ Subsingleton.elim _ _)
  exact IsZero.of_iso hz (Subobject.underlyingIso _)

omit [ConnectedSpace G.cover.left] in
/-- The whole module gives the whole sheaf. -/
theorem isIso_arrow_descentSubmoduleMap {N₁ : Submodule Λ N}
    (h : ∀ g, ∀ x ∈ N₁, ρ g x ∈ N₁) (htop : N₁ = ⊤) :
    IsIso (Subobject.mk (descentSubmoduleMap G ρ ι N₁ h)).arrow := by
  have hsurj : Function.Surjective N₁.subtype := fun x ↦
    ⟨⟨x, htop ▸ Submodule.mem_top⟩, rfl⟩
  have := G.epi_descentSheafMap N₁.subtype (ρ₂ := stableSubmoduleRep ρ N₁ h) (ρ₃ := ρ)
    (fun _ _ ↦ rfl) hsurj
  have : Epi (descentSubmoduleMap G ρ ι N₁ h) := by
    rw [descentSubmoduleMap]
    infer_instance
  have : IsIso (descentSubmoduleMap G ρ ι N₁ h) := isIso_of_mono_of_epi _
  rw [← Subobject.underlyingIso_hom_comp_eq_mk]
  infer_instance

end Transport

section Main

/-- The `Λ`-submodule of `V` underlying a submodule of `V` over the group ring. -/
def groupRingSubmodule {Λ : Type*} [CommRing Λ] {P : Type*} [Group P] {V : Type*}
    [AddCommGroup V] [Module Λ V] (ρ : Representation Λ P V)
    (W : Submodule (MonoidAlgebra Λ P) ρ.asModule) : Submodule Λ V where
  carrier := {y | ρ.asModuleEquiv.symm y ∈ W}
  add_mem' {a b} ha hb := by
    change ρ.asModuleEquiv.symm (a + b) ∈ W
    rw [map_add]
    exact W.add_mem ha hb
  zero_mem' := by
    change ρ.asModuleEquiv.symm 0 ∈ W
    rw [map_zero]
    exact W.zero_mem
  smul_mem' c y hy := by
    change ρ.asModuleEquiv.symm (c • y) ∈ W
    rw [Representation.asModuleEquiv_symm_map_smul]
    exact W.smul_mem _ hy

/-- Membership in the `Λ`-submodule underlying a submodule over the group ring. -/
theorem mem_groupRingSubmodule {Λ : Type*} [CommRing Λ] {P : Type*} [Group P] {V : Type*}
    [AddCommGroup V] [Module Λ V] (ρ : Representation Λ P V)
    (W : Submodule (MonoidAlgebra Λ P) ρ.asModule) (y : V) :
    y ∈ groupRingSubmodule ρ W ↔ ρ.asModuleEquiv.symm y ∈ W :=
  Iff.rfl

/-- The `Λ`-submodule underlying a submodule over the group ring is stable under the action. -/
theorem groupRingSubmodule_stable {Λ : Type*} [CommRing Λ] {P : Type*} [Group P] {V : Type*}
    [AddCommGroup V] [Module Λ V] (ρ : Representation Λ P V)
    (W : Submodule (MonoidAlgebra Λ P) ρ.asModule) :
    ∀ g, ∀ y ∈ groupRingSubmodule ρ W, ρ g y ∈ groupRingSubmodule ρ W := fun g y hy ↦ by
  rw [mem_groupRingSubmodule, Representation.asModuleEquiv_symm_map_rho]
  exact W.smul_mem _ hy

/-- **Stacks, Tag 0GJ0.** Let `S` be an irreducible, geometrically unibranch scheme, let `ℓ` be a
prime number and `n ≥ 1`, let `Λ` be a Noetherian ring and let `F` be a finite type, locally
constant sheaf of `Λ`-modules on `S_étale` annihilated by `ℓ ^ n`. Then there is a finite étale
morphism `f : T ⟶ S` of degree `d` prime to `ℓ` such that `f⁻¹ F` has a finite filtration whose
successive quotients are of the form `M̲_T` for finite `Λ`-modules `M`.

The filtration is a chain of subobjects of `f⁻¹ F` from the zero subobject to the whole sheaf,
each step having the constant sheaf of a finite `Λ`-module as its quotient. The degree is the
rank `d` of `f` as a finite locally free morphism.

**The unibranch hypothesis of the source is necessary**: it cannot be dropped even for `S`
irreducible (a fortiori it cannot be replaced by connectedness). Let
`S` be the nodal cubic over an algebraically closed field `k`: it is irreducible but not
geometrically unibranch at the node, and its étale fundamental group is `ℤ̂`. It is `ℙ¹_k` with
`0` and `∞` glued, and the infinite chain of copies of `ℙ¹_k`, the `i`-th glued at `∞` to
the `(i+1)`-st at `0`, is an étale covering `S̃ ⟶ S` with deck group `ℤ`. Let
`Λ = 𝔽_ℓ[t, t⁻¹]`, a Noetherian domain annihilated by `ℓ`, and let `F = S̃ ×^ℤ Λ` be the sheaf of
`Λ`-modules obtained by letting the generator of `ℤ` act on `Λ` by multiplication by `t`. It is
locally constant (constant on `S̃`), of finite type (stalks `Λ`) and annihilated by `ℓ`. For
every finite étale `f : T ⟶ S` and every connected component `T₀` of `T` (a cycle of `m ≥ 1`
copies of `ℙ¹_k`), the pullback of `S̃` to `T₀` is the `ℤ`-cover with monodromy `m`, so
`Γ(T₀, f⁻¹ F) = {v ∈ Λ | t ^ m v = v} = 0`, `t ^ m - 1` being a nonzero divisor. A constant
subsheaf `M̲_{T₀}` of `f⁻¹ F|_{T₀}` therefore has `M ⊆ Γ(T₀, M̲) = 0`; by induction along a
filtration with constant successive quotients every term restricted to `T₀` is `0`, while
`f⁻¹ F|_{T₀}` has stalks `Λ ≠ 0`. So the conclusion fails for every finite étale `f`. -/
@[stacks 0GJ0 "the filtration after a finite étale cover of degree prime to ℓ, for S \
irreducible and geometrically unibranch"]
theorem exists_finiteEtale_primeToEll_constantModuleFiltration {ℓ n : ℕ} (hℓ : ℓ.Prime)
    (_hn : 1 ≤ n) {Λ : Type r} [CommRing Λ] [IsNoetherianRing Λ]
    {S : Scheme.{u}} [IrreducibleSpace S] (hS : IsGeometricallyUnibranch S)
    (F : EtaleModules.{u, r} Λ S)
    (hF : Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant Λ S.smallEtaleTopology F)
    (hann : ∀ (U : S.Etale) (y : F.obj.obj (op U)), (ℓ ^ n) • y = 0) :
    ∃ (T : Scheme.{u}) (f : T ⟶ S) (d : ℕ), IsFinite f ∧ Etale f ∧
      Stacks.Morphisms.IsFiniteLocallyFreeOfRank f d ∧ ¬ ℓ ∣ d ∧
      ∃ X : RelSeries (ConstantFiniteModuleStep Λ ((etaleModuleInverseImage.{u, r} Λ f).obj F)),
        IsZero (Subobject.underlying.obj X.head) ∧ IsIso X.last.arrow := by
  classical
  have : Fact ℓ.Prime := ⟨hℓ⟩
  let x : GeometricPoint S := S.algClosedPoint (Classical.arbitrary S)
  obtain ⟨A, M, hM, ⟨e⟩⟩ := trivializedByPointedGaloisCovers hS x Λ F hF
  have := A.isGalois
  obtain ⟨Pₛ⟩ : Nonempty (Sylow ℓ (Aut A.obj)) := inferInstance
  let P : Subgroup (Aut A.obj) := Pₛ
  let Tq := galoisSubgroupQuotient A.obj P
  let G := galoisSubgroupQuotientCovering A.obj P hS
  have : ConnectedSpace G.cover.left := connectedSpace_left_of_isConnected A.obj inferInstance
  obtain ⟨e'⟩ := nonempty_trivialization_galoisSubgroupQuotient hS A P F M e
  let F' := (etaleModuleInverseImage.{u, r} Λ Tq.hom).obj F
  obtain ⟨ι⟩ := G.nonempty_iso_descentSheaf_coverRep e'
  let N := F'.obj.obj (op G.cover)
  have hNfin : Module.Finite Λ N := by
    let adj := constantSheafAdj ((Scheme.smallEtaleTopology Tq.left).over G.cover)
      (ModuleCat.{max (u + 1) r} Λ) (Over.mkIdTerminal (X := G.cover))
    let c : M ⟶ N := adj.unit.app M ≫ e'.hom.hom.app (op (Over.mk (𝟙 G.cover)))
    have hc : Function.Bijective c.hom :=
      ((ConcreteCategory.isIso_iff_bijective (e'.hom.hom.app (op (Over.mk (𝟙 G.cover))))).1
        inferInstance).comp (G.bijective_unit_constantSheafAdj M)
    exact Module.Finite.equiv (LinearEquiv.ofBijective c.hom hc)
  have hNann : ∀ y : N, (ℓ ^ n) • y = 0 := fun y ↦ by
    let r₀ := ((etaleModuleInverseImageRestrictionIso.{u, r} Λ Tq.hom).app F).hom.hom.app
      (op G.cover)
    have hinj : Function.Injective r₀.hom :=
      ((ConcreteCategory.isIso_iff_bijective r₀).1 inferInstance).1
    apply hinj
    rw [map_nsmul, map_zero]
    exact hann _ _
  let ρ : Representation Λ P N := G.coverRep F'
  obtain ⟨Xs, hhead, hlast⟩ := Module.exists_relSeries_trivial_action_subquotient Λ P
    ρ.asModule ℓ n hℓ Pₛ.isPGroup' (fun y ↦ hNann y)
  let Nsub := fun W ↦ groupRingSubmodule ρ W
  have hstep : ∀ j : Fin Xs.length,
      (Subobject.mk (descentSubmoduleMap G ρ ι (Nsub (Xs j.castSucc))
          (groupRingSubmodule_stable ρ _)),
        Subobject.mk (descentSubmoduleMap G ρ ι (Nsub (Xs j.succ))
          (groupRingSubmodule_stable ρ _))) ∈ ConstantFiniteModuleStep Λ F' := by
    intro j
    have hs : Xs j.castSucc ≤ Xs j.succ ∧ ∀ (g : P) (z : Xs j.succ),
        MonoidAlgebra.single g (1 : Λ) • (z : ρ.asModule) - z ∈ Xs j.castSucc := Xs.step j
    refine descentSubmoduleMap_mem_constantFiniteModuleStep G ρ ι _ _ (fun y hy ↦ hs.1 hy)
      fun g y hy ↦ ?_
    have h₁ := hs.2 g ⟨_, hy⟩
    rw [Representation.single_smul, one_smul] at h₁
    exact h₁
  refine ⟨Tq.left, Tq.hom, P.index, Tq.prop.1, Tq.prop.2,
    isFiniteLocallyFreeOfRank_galoisSubgroupQuotient A.obj P x, Pₛ.not_dvd_index,
    ⟨Xs.length, fun i ↦ Subobject.mk (descentSubmoduleMap G ρ ι (Nsub (Xs i))
      (groupRingSubmodule_stable ρ _)), hstep⟩, ?_, ?_⟩
  · refine isZero_underlying_descentSubmoduleMap G ρ ι _ ?_
    change Nsub Xs.head = ⊥
    rw [hhead]
    ext y
    simp [Nsub, mem_groupRingSubmodule]
  · refine isIso_arrow_descentSubmoduleMap G ρ ι _ ?_
    change Nsub Xs.last = ⊤
    rw [hlast]
    ext y
    simp [Nsub, mem_groupRingSubmodule]

end Main

section Induction

open ZeroObject

/-- **Induction along a filtration with constant successive quotients.** A property of sheaves of
`Λ`-modules on `X_étale` which holds for the zero sheaf and for the constant sheaves of finite
modules, is invariant under isomorphism and is closed under extensions, holds for every sheaf
admitting a finite filtration from `0` whose successive quotients are constant sheaves of finite
`Λ`-modules. -/
theorem prop_of_relSeries_constantFiniteModuleStep {X : Scheme.{u}} {Λ : Type r} [CommRing Λ]
    {F : EtaleModules.{u, r} Λ X} (Xs : RelSeries (ConstantFiniteModuleStep Λ F))
    (hhead : IsZero (Subobject.underlying.obj Xs.head)) (hlast : IsIso Xs.last.arrow)
    (Pr : ObjectProperty (EtaleModules.{u, r} Λ X)) [Pr.IsClosedUnderIsomorphisms] (h0 : Pr 0)
    (hext : ∀ Sc : ShortComplex (EtaleModules.{u, r} Λ X), Sc.ShortExact → Pr Sc.X₁ →
      Pr Sc.X₃ → Pr Sc.X₂)
    (hconst : ∀ M : ModuleCat.{max (u + 1) r} Λ, Module.Finite Λ M →
      Pr ((constantSheaf X.smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ)).obj M)) :
    Pr F := by
  have hall : ∀ i : Fin (Xs.length + 1), Pr (Subobject.underlying.obj (Xs i)) := by
    intro i
    induction i using Fin.induction with
    | zero => exact Pr.prop_of_iso ((isZero_zero _).iso hhead) h0
    | succ i ih =>
      obtain ⟨hle, M, hM, ⟨eM⟩⟩ := Xs.step i
      let f := (Xs i.castSucc).ofLE (Xs i.succ) hle
      let Sc := ShortComplex.mk f (cokernel.π f) (cokernel.condition f)
      have hSc : Sc.ShortExact := ShortComplex.ShortExact.mk'
        (ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel f)) inferInstance
        inferInstance
      exact hext Sc hSc ih (Pr.prop_of_iso eM.symm (hconst M hM))
  have hF := hall (Fin.last _)
  have := hlast
  exact Pr.prop_of_iso (asIso (Xs.last.arrow)) hF

/-- **Tag 0GJ0, in the form of an induction principle.** Under the hypotheses of
`Stacks.EtaleCohomology.exists_finiteEtale_primeToEll_constantModuleFiltration` there is a finite
étale `f : T ⟶ S` of degree prime to `ℓ` such that every property of sheaves of `Λ`-modules on
`T_étale` which is invariant under isomorphism, holds for `0` and for the constant sheaves of
finite `Λ`-modules, and is closed under extensions, holds for `f⁻¹ F`. -/
theorem exists_finiteEtale_primeToEll_prop_inverseImage {ℓ n : ℕ} (hℓ : ℓ.Prime)
    (hn : 1 ≤ n) {Λ : Type r} [CommRing Λ] [IsNoetherianRing Λ]
    {S : Scheme.{u}} [IrreducibleSpace S] (hS : IsGeometricallyUnibranch S)
    (F : EtaleModules.{u, r} Λ S)
    (hF : Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant Λ S.smallEtaleTopology F)
    (hann : ∀ (U : S.Etale) (y : F.obj.obj (op U)), (ℓ ^ n) • y = 0) :
    ∃ (T : Scheme.{u}) (f : T ⟶ S) (d : ℕ), IsFinite f ∧ Etale f ∧
      Stacks.Morphisms.IsFiniteLocallyFreeOfRank f d ∧ ¬ ℓ ∣ d ∧
      ∀ Pr : ObjectProperty (EtaleModules.{u, r} Λ T), Pr.IsClosedUnderIsomorphisms → Pr 0 →
        (∀ Sc : ShortComplex (EtaleModules.{u, r} Λ T), Sc.ShortExact → Pr Sc.X₁ →
          Pr Sc.X₃ → Pr Sc.X₂) →
        (∀ M : ModuleCat.{max (u + 1) r} Λ, Module.Finite Λ M →
          Pr ((constantSheaf T.smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ)).obj M)) →
        Pr ((etaleModuleInverseImage.{u, r} Λ f).obj F) := by
  obtain ⟨T, f, d, hfin, het, hrank, hd, Xs, hhead, hlast⟩ :=
    exists_finiteEtale_primeToEll_constantModuleFiltration hℓ hn hS F hF hann
  refine ⟨T, f, d, hfin, het, hrank, hd, fun Pr hPr h0 hext hconst ↦ ?_⟩
  have := hPr
  exact prop_of_relSeries_constantFiniteModuleStep Xs hhead hlast Pr h0 hext hconst

end Induction

end Stacks.EtaleCohomology

end
