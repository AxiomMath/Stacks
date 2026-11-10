module

public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import StacksFrontier.Topology.Sheaves.Modules.ConormalSheafStalk
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The stalk of the tensor-differentials sheaf

Let `φ : A ⟶ B` be a locally surjective morphism of sheaves of commutative rings on a topological
space `X`, let `a : R ⟶ A` be a morphism of sheaves of commutative rings, let `I` be the kernel of
`φ` and let `x` be a point of `X`.  The stalk at `x` of the middle term `B ⊗[A] Ω[A/R]` of the
conormal sequence is `(Aₓ/Iₓ) ⊗[Aₓ] Ω[Aₓ/Rₓ]`, where `Iₓ` is the kernel of `Aₓ → Bₓ`.

## Main definitions

* `Stacks.Sites.Conormal.tensorPresheafOverSource`: the presheaf
  `U ↦ (A(U)/I(U)) ⊗[A(U)] Ω[A(U)/R(U)]`, regarded as a presheaf of `A`-modules.
* `Stacks.Sites.Conormal.germTensorₛₗ`: the map
  `(A(U)/I(U)) ⊗[A(U)] Ω[A(U)/R(U)] → (Aₓ/Iₓ) ⊗[Aₓ] Ω(U)ₓ` taking germs in both factors.
* `Stacks.Sites.Conormal.tensorStalkHom`: the induced comparison map out of the stalk of
  `U ↦ (A(U)/I(U)) ⊗[A(U)] Ω[A(U)/R(U)]`.
* `Stacks.Sites.Conormal.tensorPresheafStalkKaehlerLinearEquiv`: the identification of that stalk
  with `(Aₓ/Iₓ) ⊗[Aₓ] Ω[Aₓ/Rₓ]`.
* `Stacks.Sites.Conormal.tensorDifferentialsSheafStalkLinearEquiv`: the identification
  `(B ⊗[A] Ω[A/R])ₓ ≅ (Aₓ/Iₓ) ⊗[Aₓ] Ω[Aₓ/Rₓ]`.
* `Stacks.Sites.Conormal.conormalSequenceStalkMapF`: the map induced on stalks by the left-hand
  map of the conormal sequence.

## Main results

* `Stacks.QuotientTensor.one_tmul_eq_zero_iff` and
  `Stacks.QuotientTensor.exists_eq_one_tmul`: in `(S/J) ⊗[S] M` every element is `1 ⊗ m`, and
  `1 ⊗ m = 0` exactly when `m ∈ J • M`.
* `Stacks.Sites.Conormal.exists_germ_eq_of_mem_stalkKernelIdeal_smul`: every element of
  `Iₓ · Ω(U)ₓ` is the germ of a section of `I(U) · Ω[A(U)/R(U)]`.
* `Stacks.Sites.Conormal.tensorStalkHom_injective` and
  `Stacks.Sites.Conormal.tensorStalkHom_surjective`: the comparison map is bijective.
* `Stacks.Sites.Conormal.tensorDifferentialsSheafStalkLinearEquiv_germ_tensorDifferential`: the
  identification carries the germ of the local section `1 ⊗ d f` to `1 ⊗ d (fₓ)`.
* `Stacks.Sites.Conormal.conormalSequenceStalkMapF_toCotangent`: the stalk of the left-hand map of
  the conormal sequence is the degree `-1` differential of the naive cotangent complex of
  `Rₓ → Aₓ → Aₓ/Iₓ`: it sends the conormal class of `y ∈ Iₓ` to `1 ⊗ d y`.

## References

* [Stacks Project, Tag 08TL](https://stacks.math.columbia.edu/tag/08TL)
* [Stacks Project, Tag 08TE](https://stacks.math.columbia.edu/tag/08TE)
* [Stacks Project, Tag 08TS](https://stacks.math.columbia.edu/tag/08TS)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite TensorProduct

universe u

noncomputable section

/-! ### Tensoring a module with a quotient of the ring -/

namespace Stacks.QuotientTensor

variable {S : Type u} [CommRing S] (J : Ideal S) {M : Type u} [AddCommGroup M] [Module S M]

/-- On `(S/J) ⊗[S] M` the action of a scalar of `S` agrees with the action of its class in
`S/J`. -/
theorem quotientMk_smul (r : S) (t : (S ⧸ J) ⊗[S] M) :
    (Ideal.Quotient.mk J r) • t = r • t := by
  induction t using TensorProduct.inductionOn with
  | tmul b m => rw [TensorProduct.smul_tmul', TensorProduct.smul_tmul']; congr 1
  | add y z hy hz => rw [smul_add, smul_add, hy, hz]

/-- A tensor `1 ⊗ m` in `(S/J) ⊗[S] M` vanishes exactly when `m` lies in `J · M`. -/
theorem one_tmul_eq_zero_iff (m : M) :
    (1 : S ⧸ J) ⊗ₜ[S] m = 0 ↔ m ∈ J • (⊤ : Submodule S M) := by
  rw [← (TensorProduct.quotTensorEquivQuotSMul M J).map_eq_zero_iff,
    TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul, Submodule.Quotient.mk_eq_zero]

/-- Every element of `(S/J) ⊗[S] M` is of the form `1 ⊗ m`. -/
theorem exists_eq_one_tmul (t : (S ⧸ J) ⊗[S] M) : ∃ m : M, t = 1 ⊗ₜ[S] m := by
  obtain ⟨m, hm⟩ := Submodule.Quotient.mk_surjective (J • (⊤ : Submodule S M))
    (TensorProduct.quotTensorEquivQuotSMul M J t)
  refine ⟨m, ?_⟩
  rw [← TensorProduct.quotTensorEquivQuotSMul_symm_mk (M := M) J m, hm,
    LinearEquiv.symm_apply_apply]

end Stacks.QuotientTensor

namespace Stacks.Sites.Conormal

/-! ### The comparison map on sections -/

section Presheaf

variable {X : TopCat.{u}} {A B : X.Presheaf CommRingCat.{u}} (φ : A ⟶ B)
  {R : X.Presheaf CommRingCat.{u}} (a : R ⟶ A) (x : X)

/-- The presheaf `U ↦ (A(U)/I(U)) ⊗[A(U)] Ω[A(U)/R(U)]`, regarded as a presheaf of modules over
`A` by restriction of scalars along `A ⟶ A/I`. -/
def tensorPresheafOverSource : PresheafOfModules.{u} (A ⋙ forget₂ CommRingCat RingCat) :=
  (PresheafOfModules.restrictScalars (toQuotientRingHom φ)).obj (tensorPresheaf φ a)

/-- The map `A(U)/I(U) → Aₓ/Iₓ` induced by taking germs at `x`, semilinear over the germ map of
`A`. -/
def germQuotientₛₗ (U : Opens X) (hx : x ∈ U) :
    (A.obj (op U) ⧸ kernelIdeal φ (op U)) →ₛₗ[(A.germ U x hx).hom]
      (ToType (A.stalk x) ⧸ stalkKernelIdeal φ x) where
  toFun := Ideal.quotientMap (stalkKernelIdeal φ x) (A.germ U x hx).hom
    (kernelIdeal_le_comap_germ φ x U hx)
  map_add' := map_add _
  map_smul' r y := by
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    change Ideal.Quotient.mk _ ((A.germ U x hx).hom (r * y)) = _
    rw [map_mul]
    rfl

/-- The germ map of the presheaf of sectionwise relative differentials, semilinear over the germ
map of `A`. -/
def germOmegaₛₗ (U : Opens X) (hx : x ∈ U) :
    (differentialsPresheaf a).obj (op U) →ₛₗ[(A.germ U x hx).hom]
      ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
        (differentialsPresheaf a).presheaf x) where
  toFun := TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) (differentialsPresheaf a).presheaf U x hx
  map_add' := map_add _
  map_smul' r ω := PresheafOfModules.germ_smul (differentialsPresheaf a) x U hx r ω

/-- The comparison map on sections: taking germs in both tensor factors. -/
def germTensorₛₗ (U : Opens X) (hx : x ∈ U) :
    ((A.obj (op U) ⧸ kernelIdeal φ (op U)) ⊗[A.obj (op U)]
        ((differentialsPresheaf a).obj (op U))) →ₛₗ[(A.germ U x hx).hom]
      ((ToType (A.stalk x) ⧸ stalkKernelIdeal φ x) ⊗[ToType (A.stalk x)]
        ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
          (differentialsPresheaf a).presheaf x)) :=
  TensorProduct.map (germQuotientₛₗ φ x U hx) (germOmegaₛₗ a x U hx)

/-- The comparison map on sections is compatible with restriction to a smaller neighbourhood of
`x`. -/
theorem germTensorₛₗ_map {U V : Opens X} (i : V ⟶ U) (hV : x ∈ V)
    (t : (tensorPresheafOverSource φ a).obj (op U)) :
    germTensorₛₗ φ a x V hV ((tensorPresheafOverSource φ a).map i.op t) =
      germTensorₛₗ φ a x U (i.le hV) t := by
  change germTensorₛₗ φ a x V hV (tensorMapₛₗ φ a i.op t) = _
  induction t using TensorProduct.inductionOn with
  | tmul b ω =>
      rw [tensorMapₛₗ, TensorProduct.map_tmul, germTensorₛₗ, germTensorₛₗ, TensorProduct.map_tmul,
        TensorProduct.map_tmul]
      refine congrArg₂ (fun (q : ToType (A.stalk x) ⧸ stalkKernelIdeal φ x)
        (ω : ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
          (differentialsPresheaf a).presheaf x)) => q ⊗ₜ[ToType (A.stalk x)] ω) ?_ ?_
      · obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
        change Ideal.Quotient.mk _ ((A.germ V x hV).hom ((A.map i.op).hom b)) =
          Ideal.Quotient.mk _ ((A.germ U x (i.le hV)).hom b)
        exact congrArg (Ideal.Quotient.mk (stalkKernelIdeal φ x))
          (TopCat.Presheaf.germ_res_apply A i x hV b)
      · exact TopCat.Presheaf.germ_res_apply (C := AddCommGrpCat.{u})
          (differentialsPresheaf a).presheaf i x hV ω
  | add y z hy hz => rw [map_add, map_add, map_add, hy, hz]

/-- The comparison map on sections is semilinear over the germ map of `A`, for the action of
`A(U)` through `A(U)/I(U)`. -/
theorem germTensorₛₗ_smul (U : Opens X) (hx : x ∈ U) (r : A.obj (op U))
    (t : (A.obj (op U) ⧸ kernelIdeal φ (op U)) ⊗[A.obj (op U)]
      ((differentialsPresheaf a).obj (op U))) :
    germTensorₛₗ φ a x U hx (Ideal.Quotient.mk (kernelIdeal φ (op U)) r • t) =
      (A.germ U x hx).hom r • germTensorₛₗ φ a x U hx t := by
  rw [Stacks.QuotientTensor.quotientMk_smul]
  exact map_smulₛₗ (germTensorₛₗ φ a x U hx) r t

/-! ### The comparison map out of the stalk -/

/-- The tensor product `(Aₓ/Iₓ) ⊗[Aₓ] Ω(U)ₓ` as a cocone over the diagram of the tensor products
of the sections near `x`. -/
def tensorStalkCocone :
    Cocone ((OpenNhds.inclusion x).op ⋙ (tensorPresheafOverSource φ a).presheaf) where
  pt := AddCommGrpCat.of ((ToType (A.stalk x) ⧸ stalkKernelIdeal φ x) ⊗[ToType (A.stalk x)]
    ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
      (differentialsPresheaf a).presheaf x))
  ι :=
    { app := fun V => AddCommGrpCat.ofHom
        (AddMonoidHom.mk' (germTensorₛₗ φ a x V.unop.1 V.unop.2) (map_add _))
      naturality := by
        intro V W f
        ext t
        exact germTensorₛₗ_map φ a x ((OpenNhds.inclusion x).map f.unop) W.unop.2 t }

/-- The comparison homomorphism from the stalk at `x` of the presheaf
`U ↦ (A(U)/I(U)) ⊗[A(U)] Ω[A(U)/R(U)]` to `(Aₓ/Iₓ) ⊗[Aₓ] Ω(U)ₓ`. -/
def tensorStalkHom :
    ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
        (tensorPresheafOverSource φ a).presheaf x) →+
      ((ToType (A.stalk x) ⧸ stalkKernelIdeal φ x) ⊗[ToType (A.stalk x)]
        ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
          (differentialsPresheaf a).presheaf x)) :=
  (colimit.desc _ (tensorStalkCocone φ a x)).hom

/-- The comparison map sends the germ of a section to its image under the comparison map on
sections. -/
theorem tensorStalkHom_germ (U : Opens X) (hx : x ∈ U)
    (t : (tensorPresheafOverSource φ a).obj (op U)) :
    tensorStalkHom φ a x (TopCat.Presheaf.germ (C := AddCommGrpCat.{u})
        (tensorPresheafOverSource φ a).presheaf U x hx t) = germTensorₛₗ φ a x U hx t :=
  ConcreteCategory.congr_hom
    (colimit.ι_desc (tensorStalkCocone φ a x) (op (⟨U, hx⟩ : OpenNhds x))) t

/-- The comparison map sends the germ of `1 ⊗ ω` to `1 ⊗ ωₓ`. -/
theorem tensorStalkHom_germ_one_tmul (U : Opens X) (hx : x ∈ U)
    (ω : (differentialsPresheaf a).obj (op U)) :
    tensorStalkHom φ a x (TopCat.Presheaf.germ (C := AddCommGrpCat.{u})
        (tensorPresheafOverSource φ a).presheaf U x hx
        ((1 : A.obj (op U) ⧸ kernelIdeal φ (op U)) ⊗ₜ[A.obj (op U)] ω)) =
      (1 : ToType (A.stalk x) ⧸ stalkKernelIdeal φ x) ⊗ₜ[ToType (A.stalk x)]
        TopCat.Presheaf.germ (C := AddCommGrpCat.{u})
          (differentialsPresheaf a).presheaf U x hx ω := by
  refine (tensorStalkHom_germ φ a x U hx _).trans ?_
  refine (TensorProduct.map_tmul (germQuotientₛₗ φ x U hx) (germOmegaₛₗ a x U hx) 1 ω).trans ?_
  exact congrArg (fun q : ToType (A.stalk x) ⧸ stalkKernelIdeal φ x =>
    q ⊗ₜ[ToType (A.stalk x)] TopCat.Presheaf.germ (C := AddCommGrpCat.{u})
      (differentialsPresheaf a).presheaf U x hx ω)
    (map_one (Ideal.quotientMap (stalkKernelIdeal φ x) (A.germ U x hx).hom
      (kernelIdeal_le_comap_germ φ x U hx)))

/-- The comparison map is linear over the stalk of `A`. -/
theorem tensorStalkHom_smul (r : ToType (A.stalk x))
    (ξ : ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
      (tensorPresheafOverSource φ a).presheaf x)) :
    tensorStalkHom φ a x (r • ξ) = r • tensorStalkHom φ a x ξ := by
  obtain ⟨Ur, hr, r₁, rfl⟩ := A.exists_germ_eq r
  obtain ⟨Uc, hc, t₁, rfl⟩ := TopCat.Presheaf.exists_germ_eq (C := AddCommGrpCat.{u})
    (tensorPresheafOverSource φ a).presheaf ξ
  have hU : x ∈ Ur ⊓ Uc := ⟨hr, hc⟩
  have er := TopCat.Presheaf.germ_res_apply A
    (homOfLE (inf_le_left : Ur ⊓ Uc ≤ Ur)) x hU r₁
  have ec := TopCat.Presheaf.germ_res_apply (C := AddCommGrpCat.{u})
    (tensorPresheafOverSource φ a).presheaf (homOfLE (inf_le_right : Ur ⊓ Uc ≤ Uc)) x hU t₁
  rw [← er, ← ec]
  refine (congrArg (tensorStalkHom φ a x)
    (PresheafOfModules.germ_smul (tensorPresheafOverSource φ a) x (Ur ⊓ Uc) hU _ _).symm).trans ?_
  refine (tensorStalkHom_germ φ a x (Ur ⊓ Uc) hU _).trans ?_
  refine (germTensorₛₗ_smul φ a x (Ur ⊓ Uc) hU _ _).trans ?_
  exact congrArg _ (tensorStalkHom_germ φ a x (Ur ⊓ Uc) hU _).symm

/-! ### Germs of sections of the tensor presheaf -/

/-- Every element of the stalk of `U ↦ (A(U)/I(U)) ⊗[A(U)] Ω[A(U)/R(U)]` is the germ of a section
of the form `1 ⊗ ω`. -/
theorem exists_germ_eq_one_tmul (ξ : ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
    (tensorPresheafOverSource φ a).presheaf x)) :
    ∃ (U : Opens X) (hx : x ∈ U) (ω : (differentialsPresheaf a).obj (op U)),
      TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) (tensorPresheafOverSource φ a).presheaf U x hx
        ((1 : A.obj (op U) ⧸ kernelIdeal φ (op U)) ⊗ₜ[A.obj (op U)] ω) = ξ := by
  obtain ⟨U, hU, t, rfl⟩ := TopCat.Presheaf.exists_germ_eq (C := AddCommGrpCat.{u})
    (tensorPresheafOverSource φ a).presheaf ξ
  obtain ⟨ω, rfl⟩ := Stacks.QuotientTensor.exists_eq_one_tmul (kernelIdeal φ (op U))
    (M := (differentialsPresheaf a).obj (op U)) t
  exact ⟨U, hU, ω, rfl⟩

/-- Restriction to a smaller open set carries `1 ⊗ ω` to `1 ⊗ ω|ᵥ`. -/
theorem tensorPresheafOverSource_map_one_tmul {U V : Opens X} (i : V ⟶ U)
    (ω : (differentialsPresheaf a).obj (op U)) :
    ((tensorPresheafOverSource φ a).presheaf.map i.op).hom
        ((1 : A.obj (op U) ⧸ kernelIdeal φ (op U)) ⊗ₜ[A.obj (op U)] ω) =
      (1 : A.obj (op V) ⧸ kernelIdeal φ (op V)) ⊗ₜ[A.obj (op V)]
        (differentialsPresheaf a).restrictₛₗ i.op ω := by
  refine Eq.trans (show ((tensorPresheafOverSource φ a).presheaf.map i.op).hom
      ((1 : A.obj (op U) ⧸ kernelIdeal φ (op U)) ⊗ₜ[A.obj (op U)] ω) =
      tensorMapₛₗ φ a i.op ((1 : A.obj (op U) ⧸ kernelIdeal φ (op U)) ⊗ₜ[A.obj (op U)] ω)
    from rfl) ?_
  refine (TensorProduct.map_tmul _ _ _ _).trans ?_
  exact congrArg (fun q : A.obj (op V) ⧸ kernelIdeal φ (op V) =>
      q ⊗ₜ[A.obj (op V)] (differentialsPresheaf a).restrictₛₗ i.op ω)
    (map_one ((quotientPresheaf φ).map i.op).hom)

/-- Restriction to a smaller open set carries `I(U) · Ω[A(U)/R(U)]` into
`I(V) · Ω[A(V)/R(V)]`. -/
theorem map_mem_kernelIdeal_smul {U V : Opens X} (i : V ⟶ U)
    (ω : (differentialsPresheaf a).obj (op U))
    (hω : ω ∈ kernelIdeal φ (op U) • (⊤ : Submodule (A.obj (op U))
      ((differentialsPresheaf a).obj (op U)))) :
    (differentialsPresheaf a).restrictₛₗ i.op ω ∈ kernelIdeal φ (op V) •
      (⊤ : Submodule (A.obj (op V)) ((differentialsPresheaf a).obj (op V))) := by
  refine Submodule.smul_induction_on hω ?_ ?_
  · intro r hr n _
    refine (map_smulₛₗ ((differentialsPresheaf a).restrictₛₗ i.op) r n).symm ▸ ?_
    exact Submodule.smul_mem_smul (map_kernel φ i.op hr) Submodule.mem_top
  · intro y z hy hz
    exact (map_add ((differentialsPresheaf a).restrictₛₗ i.op) y z).symm ▸ add_mem hy hz

/-- **Every element of `Iₓ · Ω(U)ₓ` is the germ of a section of `I(U) · Ω[A(U)/R(U)]`.** -/
theorem exists_germ_eq_of_mem_stalkKernelIdeal_smul
    (ζ : ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
      (differentialsPresheaf a).presheaf x))
    (hζ : ζ ∈ stalkKernelIdeal φ x • (⊤ : Submodule (ToType (A.stalk x))
      (ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
        (differentialsPresheaf a).presheaf x)))) :
    ∃ (U : Opens X) (hx : x ∈ U) (ω : (differentialsPresheaf a).obj (op U)),
      ω ∈ kernelIdeal φ (op U) • (⊤ : Submodule (A.obj (op U))
        ((differentialsPresheaf a).obj (op U))) ∧
      TopCat.Presheaf.germ (C := AddCommGrpCat.{u})
        (differentialsPresheaf a).presheaf U x hx ω = ζ := by
  refine Submodule.smul_induction_on hζ ?_ ?_
  · intro c hc ζ' _
    obtain ⟨U₁, h₁, c₀, hc₀, rfl⟩ := exists_germ_eq_of_mem_stalkKernelIdeal φ x c hc
    obtain ⟨U₂, h₂, ω₀, rfl⟩ := TopCat.Presheaf.exists_germ_eq (C := AddCommGrpCat.{u})
      (differentialsPresheaf a).presheaf ζ'
    have hx : x ∈ U₁ ⊓ U₂ := ⟨h₁, h₂⟩
    refine ⟨U₁ ⊓ U₂, hx, (A.map (homOfLE inf_le_left : U₁ ⊓ U₂ ⟶ U₁).op).hom c₀ •
      (differentialsPresheaf a).restrictₛₗ (homOfLE inf_le_right : U₁ ⊓ U₂ ⟶ U₂).op ω₀, ?_, ?_⟩
    · exact Submodule.smul_mem_smul (map_kernel φ _ hc₀) Submodule.mem_top
    · refine (PresheafOfModules.germ_smul (differentialsPresheaf a) x (U₁ ⊓ U₂) hx _ _).trans ?_
      exact congrArg₂ (fun (r : ToType (A.stalk x))
          (ω : ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
            (differentialsPresheaf a).presheaf x)) => r • ω)
        (TopCat.Presheaf.germ_res_apply A _ x hx c₀)
        (TopCat.Presheaf.germ_res_apply (C := AddCommGrpCat.{u})
          (differentialsPresheaf a).presheaf _ x hx ω₀)
  · rintro ζ₁ ζ₂ ⟨U₁, h₁, ω₁, hm₁, e₁⟩ ⟨U₂, h₂, ω₂, hm₂, e₂⟩
    have hx : x ∈ U₁ ⊓ U₂ := ⟨h₁, h₂⟩
    refine ⟨U₁ ⊓ U₂, hx,
      (differentialsPresheaf a).restrictₛₗ (homOfLE inf_le_left : U₁ ⊓ U₂ ⟶ U₁).op ω₁ +
        (differentialsPresheaf a).restrictₛₗ (homOfLE inf_le_right : U₁ ⊓ U₂ ⟶ U₂).op ω₂, ?_, ?_⟩
    · exact add_mem (map_mem_kernelIdeal_smul φ a _ ω₁ hm₁) (map_mem_kernelIdeal_smul φ a _ ω₂ hm₂)
    · refine (map_add (TopCat.Presheaf.germ (C := AddCommGrpCat.{u})
        (differentialsPresheaf a).presheaf (U₁ ⊓ U₂) x hx).hom _ _).trans ?_
      exact congrArg₂ (· + ·)
        ((TopCat.Presheaf.germ_res_apply (C := AddCommGrpCat.{u})
          (differentialsPresheaf a).presheaf _ x hx ω₁).trans e₁)
        ((TopCat.Presheaf.germ_res_apply (C := AddCommGrpCat.{u})
          (differentialsPresheaf a).presheaf _ x hx ω₂).trans e₂)

/-! ### The comparison map is bijective -/

/-- The comparison map is surjective: every element of `(Aₓ/Iₓ) ⊗[Aₓ] Ω(U)ₓ` is `1 ⊗ ωₓ` for a
section `ω` of the sectionwise differentials over a neighbourhood of `x`. -/
theorem tensorStalkHom_surjective : Function.Surjective (tensorStalkHom φ a x) := by
  intro z
  obtain ⟨ζ, rfl⟩ := Stacks.QuotientTensor.exists_eq_one_tmul (stalkKernelIdeal φ x) z
  obtain ⟨U, hU, ω, rfl⟩ := TopCat.Presheaf.exists_germ_eq (C := AddCommGrpCat.{u})
    (differentialsPresheaf a).presheaf ζ
  exact ⟨_, tensorStalkHom_germ_one_tmul φ a x U hU ω⟩

/-- The comparison map is injective. -/
theorem tensorStalkHom_injective : Function.Injective (tensorStalkHom φ a x) := by
  refine (injective_iff_map_eq_zero (tensorStalkHom φ a x)).mpr fun ξ hξ ↦ ?_
  obtain ⟨U, hU, ω, rfl⟩ := exists_germ_eq_one_tmul φ a x ξ
  have h1 := (tensorStalkHom_germ_one_tmul φ a x U hU ω).symm.trans hξ
  have hmem := (Stacks.QuotientTensor.one_tmul_eq_zero_iff (stalkKernelIdeal φ x) _).mp h1
  obtain ⟨V, hV, η, hη, hηg⟩ := exists_germ_eq_of_mem_stalkKernelIdeal_smul φ a x _ hmem
  obtain ⟨W, hW, iU, iV, hWe⟩ := TopCat.Presheaf.germ_eq (C := AddCommGrpCat.{u})
    (differentialsPresheaf a).presheaf x hU hV ω η hηg.symm
  have hmemW : (differentialsPresheaf a).restrictₛₗ iU.op ω ∈
      kernelIdeal φ (op W) • (⊤ : Submodule (A.obj (op W))
        ((differentialsPresheaf a).obj (op W))) := by
    refine hWe.symm ▸ ?_
    exact map_mem_kernelIdeal_smul φ a iV η hη
  have hzero : ((tensorPresheafOverSource φ a).presheaf.map iU.op).hom
      ((1 : A.obj (op U) ⧸ kernelIdeal φ (op U)) ⊗ₜ[A.obj (op U)] ω) = 0 :=
    (tensorPresheafOverSource_map_one_tmul φ a iU ω).trans
      ((Stacks.QuotientTensor.one_tmul_eq_zero_iff _ _).mpr hmemW)
  refine (TopCat.Presheaf.germ_res_apply (C := AddCommGrpCat.{u})
    (tensorPresheafOverSource φ a).presheaf iU x hW _).symm.trans ?_
  refine (congrArg (TopCat.Presheaf.germ (C := AddCommGrpCat.{u})
    (tensorPresheafOverSource φ a).presheaf W x hW).hom hzero).trans ?_
  exact map_zero _

/-! ### The stalk of the tensor presheaf -/

/-- The comparison map, as a linear map over the stalk of `A`. -/
def tensorStalkLinearMap :
    ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
        (tensorPresheafOverSource φ a).presheaf x) →ₗ[ToType (A.stalk x)]
      ((ToType (A.stalk x) ⧸ stalkKernelIdeal φ x) ⊗[ToType (A.stalk x)]
        ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
          (differentialsPresheaf a).presheaf x)) where
  toFun := tensorStalkHom φ a x
  map_add' := map_add (tensorStalkHom φ a x)
  map_smul' := tensorStalkHom_smul φ a x

/-- **Forming `(A/I) ⊗[A] Ω` commutes with stalks.**  The stalk at `x` of the presheaf
`U ↦ (A(U)/I(U)) ⊗[A(U)] Ω[A(U)/R(U)]` is `(Aₓ/Iₓ) ⊗[Aₓ] Ω(U)ₓ`, where `Ω(U)ₓ` is the stalk of the
presheaf of sectionwise differentials. -/
def tensorPresheafStalkLinearEquiv :
    ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
        (tensorPresheafOverSource φ a).presheaf x) ≃ₗ[ToType (A.stalk x)]
      ((ToType (A.stalk x) ⧸ stalkKernelIdeal φ x) ⊗[ToType (A.stalk x)]
        ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
          (differentialsPresheaf a).presheaf x)) :=
  LinearEquiv.ofBijective (tensorStalkLinearMap φ a x)
    ⟨tensorStalkHom_injective φ a x, tensorStalkHom_surjective φ a x⟩

/-- The equivalence `tensorPresheafStalkLinearEquiv` is the comparison map `tensorStalkHom`. -/
@[simp]
theorem tensorPresheafStalkLinearEquiv_apply
    (ξ : ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
      (tensorPresheafOverSource φ a).presheaf x)) :
    tensorPresheafStalkLinearEquiv φ a x ξ = tensorStalkHom φ a x ξ := rfl

section Kaehler

variable [DecidableEq (OrderDual (TopologicalSpace.OpenNhds x))]

/-- **The stalk of the presheaf `U ↦ (A(U)/I(U)) ⊗[A(U)] Ω[A(U)/R(U)]` is
`(Aₓ/Iₓ) ⊗[Aₓ] Ω[Aₓ/Rₓ]`.** -/
def tensorPresheafStalkKaehlerLinearEquiv :
    letI := Stacks.RelativeDifferentialStalk.algebraStalk a x
    ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
        (tensorPresheafOverSource φ a).presheaf x) ≃ₗ[ToType (A.stalk x)]
      ((ToType (A.stalk x) ⧸ stalkKernelIdeal φ x) ⊗[ToType (A.stalk x)]
        KaehlerDifferential (ToType (R.stalk x)) (ToType (A.stalk x))) :=
  letI := Stacks.RelativeDifferentialStalk.algebraStalk a x
  (tensorPresheafStalkLinearEquiv φ a x).trans
    (TensorProduct.congr (LinearEquiv.refl _ _)
      (Stacks.RelativeDifferentialStalk.stalkLinearEquiv a x))

/-- The identification carries the germ of `1 ⊗ ω` to `1 ⊗ ωₓ`. -/
theorem tensorPresheafStalkKaehlerLinearEquiv_germ_one_tmul (U : Opens X) (hx : x ∈ U)
    (ω : (differentialsPresheaf a).obj (op U)) :
    letI := Stacks.RelativeDifferentialStalk.algebraStalk a x
    tensorPresheafStalkKaehlerLinearEquiv φ a x
        (TopCat.Presheaf.germ (C := AddCommGrpCat.{u})
          (tensorPresheafOverSource φ a).presheaf U x hx
          ((1 : A.obj (op U) ⧸ kernelIdeal φ (op U)) ⊗ₜ[A.obj (op U)] ω)) =
      (1 : ToType (A.stalk x) ⧸ stalkKernelIdeal φ x) ⊗ₜ[ToType (A.stalk x)]
        Stacks.RelativeDifferentialStalk.stalkLinearEquiv a x
          (TopCat.Presheaf.germ (C := AddCommGrpCat.{u})
            (differentialsPresheaf a).presheaf U x hx ω) := by
  let := Stacks.RelativeDifferentialStalk.algebraStalk a x
  refine Eq.trans (congrArg (TensorProduct.congr (LinearEquiv.refl _ _)
      (Stacks.RelativeDifferentialStalk.stalkLinearEquiv a x))
      (tensorStalkHom_germ_one_tmul φ a x U hx ω)) ?_
  exact TensorProduct.congr_tmul (LinearEquiv.refl _ _)
    (Stacks.RelativeDifferentialStalk.stalkLinearEquiv a x) 1 _

/-- **The identification carries universal differentials to universal differentials.**  The germ
at `x` of the local section `1 ⊗ d f` goes to `1 ⊗ d (fₓ)`. -/
theorem tensorPresheafStalkKaehlerLinearEquiv_germ_one_tmul_d (U : Opens X) (hx : x ∈ U)
    (f : A.obj (op U)) :
    letI := Stacks.RelativeDifferentialStalk.algebraStalk a x
    tensorPresheafStalkKaehlerLinearEquiv φ a x
        (TopCat.Presheaf.germ (C := AddCommGrpCat.{u})
          (tensorPresheafOverSource φ a).presheaf U x hx
          ((1 : A.obj (op U) ⧸ kernelIdeal φ (op U)) ⊗ₜ[A.obj (op U)]
            CommRingCat.KaehlerDifferential.d (f := a.app (op U)) f)) =
      (1 : ToType (A.stalk x) ⧸ stalkKernelIdeal φ x) ⊗ₜ[ToType (A.stalk x)]
        KaehlerDifferential.D (ToType (R.stalk x)) (ToType (A.stalk x))
          ((A.germ U x hx).hom f) := by
  let := Stacks.RelativeDifferentialStalk.algebraStalk a x
  refine (tensorPresheafStalkKaehlerLinearEquiv_germ_one_tmul φ a x U hx _).trans ?_
  exact congrArg (fun ω : KaehlerDifferential (ToType (R.stalk x)) (ToType (A.stalk x)) =>
      (1 : ToType (A.stalk x) ⧸ stalkKernelIdeal φ x) ⊗ₜ[ToType (A.stalk x)] ω)
    (Stacks.RelativeDifferentialStalk.stalkLinearEquiv_germ_D a x
      (OrderDual.toDual (⟨U, hx⟩ : TopologicalSpace.OpenNhds x)) f)

end Kaehler

end Presheaf

/-! ### The stalk of the tensor-differentials sheaf -/

section Sheaf

variable {X : TopCat.{u}} (R A B : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u})
  (a : R ⟶ A) (φ : A ⟶ B)
  [Presheaf.IsLocallySurjective (Opens.grothendieckTopology X) φ.hom] (x : X)

/-- The tensor-differentials sheaf `B ⊗[A] Ω[A/R]`, regarded as a presheaf of modules over `A` by
restriction of scalars along `A ⟶ A/I ⟶ B`. -/
def tensorSheafOverSource :
    PresheafOfModules.{u} (A.obj ⋙ forget₂ CommRingCat RingCat) :=
  (PresheafOfModules.restrictScalars (toQuotientRingHom φ.hom)).obj
    ((PresheafOfModules.restrictScalars
        (quotientToRingSheaf (Opens.grothendieckTopology X) A B φ)).obj
      ((_root_.SheafOfModules.forget _).obj
        (tensorDifferentialsSheaf (Opens.grothendieckTopology X) R A B a φ)))

/-- **Sheafifying the tensor presheaf does not change its stalks**: the universe lift followed by
the unit of sheafification induces an isomorphism on stalks at `x`. -/
theorem isIso_stalkFunctor_map_tensorSheafificationUnit :
    IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      ((PresheafOfModules.toPresheaf (quotientPresheaf φ.hom ⋙ forget₂ CommRingCat RingCat)).map
        ((liftModulesIso (tensorPresheaf φ.hom a.hom)).hom ≫
          (PresheafOfModules.sheafificationAdjunction.{u}
              (quotientToRingSheaf (Opens.grothendieckTopology X) A B φ)).unit.app
            ((liftModules.{u, u, u, u} _).obj (tensorPresheaf φ.hom a.hom))))) := by
  have h2 : IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      ((PresheafOfModules.toPresheaf (quotientPresheaf φ.hom ⋙ forget₂ CommRingCat RingCat)).map
        ((PresheafOfModules.sheafificationAdjunction.{u}
            (quotientToRingSheaf (Opens.grothendieckTopology X) A B φ)).unit.app
          ((liftModules.{u, u, u, u} _).obj (tensorPresheaf φ.hom a.hom))))) :=
    TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat.{u}
      ((liftModules.{u, u, u, u} (quotientPresheaf φ.hom ⋙ forget₂ CommRingCat RingCat)).obj
        (tensorPresheaf φ.hom a.hom)).presheaf
  rw [Functor.map_comp, Functor.map_comp]
  infer_instance

/-- The universe lift followed by the unit of sheafification, as a morphism of presheaves of
`A`-modules from the tensor presheaf to the tensor-differentials sheaf. -/
def toTensorSheafOverSource :
    tensorPresheafOverSource φ.hom a.hom ⟶ tensorSheafOverSource R A B a φ :=
  (PresheafOfModules.restrictScalars (toQuotientRingHom φ.hom)).map
    ((liftModulesIso (tensorPresheaf φ.hom a.hom)).hom ≫
      (PresheafOfModules.sheafificationAdjunction.{u}
          (quotientToRingSheaf (Opens.grothendieckTopology X) A B φ)).unit.app
        ((liftModules.{u, u, u, u} _).obj (tensorPresheaf φ.hom a.hom)))

/-- On sections the comparison morphism is the image of a tensor under the unit of
sheafification. -/
theorem toTensorSheafOverSource_app (U : Opens X)
    (t : (tensorPresheafOverSource φ.hom a.hom).obj (op U)) :
    (toTensorSheafOverSource R A B a φ).app (op U) t =
      toAssociatedModule (Opens.grothendieckTopology X) A B φ
        (tensorPresheaf φ.hom a.hom) (op U) t :=
  rfl

/-- The comparison morphism from the tensor presheaf to the tensor-differentials sheaf induces an
isomorphism on stalks at `x`. -/
theorem isIso_stalkFunctor_map_toTensorSheafOverSource :
    IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      ((PresheafOfModules.toPresheaf (A.obj ⋙ forget₂ CommRingCat RingCat)).map
        (toTensorSheafOverSource R A B a φ))) :=
  isIso_stalkFunctor_map_tensorSheafificationUnit R A B a φ x

/-- The stalk of the tensor-differentials sheaf is a module over the stalk of `A`, through the
restriction of scalars along `A ⟶ A/I ⟶ B`. -/
instance moduleStalkTensorDifferentialsSheaf :
    Module (ToType (TopCat.Presheaf.stalk A.obj x))
      (ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
        (tensorDifferentialsSheaf (Opens.grothendieckTopology X) R A B a φ).val.presheaf x)) :=
  inferInstanceAs (Module (ToType (TopCat.Presheaf.stalk A.obj x))
    (ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
      (tensorSheafOverSource R A B a φ).presheaf x)))

/-- The stalk of the tensor presheaf, identified with the stalk of the tensor-differentials
sheaf. -/
def tensorSheafStalkSheafifyLinearEquiv :
    ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
        (tensorPresheafOverSource φ.hom a.hom).presheaf x)
      ≃ₗ[ToType (TopCat.Presheaf.stalk A.obj x)]
      ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
        (tensorDifferentialsSheaf (Opens.grothendieckTopology X) R A B a φ).val.presheaf x) :=
  Stacks.RelativeDifferentialStalk.stalkLinearEquivOfIsIso (R := A.obj) _ _
    (toTensorSheafOverSource R A B a φ) x
    (isIso_stalkFunctor_map_toTensorSheafOverSource R A B a φ x)

/-- The identification of the stalk of the tensor presheaf with the stalk of the
tensor-differentials sheaf carries the germ of a tensor to the germ of the corresponding section of
the sheaf. -/
theorem tensorSheafStalkSheafifyLinearEquiv_germ (U : Opens X) (hx : x ∈ U)
    (t : (tensorPresheafOverSource φ.hom a.hom).obj (op U)) :
    tensorSheafStalkSheafifyLinearEquiv R A B a φ x
        (TopCat.Presheaf.germ (C := AddCommGrpCat.{u})
          (tensorPresheafOverSource φ.hom a.hom).presheaf U x hx t) =
      TopCat.Presheaf.germ (C := AddCommGrpCat.{u})
        (tensorDifferentialsSheaf (Opens.grothendieckTopology X) R A B a φ).val.presheaf U x hx
        (toAssociatedModule (Opens.grothendieckTopology X) A B φ
          (tensorPresheaf φ.hom a.hom) (op U) t) :=
  Stacks.RelativeDifferentialStalk.stalkLinearEquivOfIsIso_germ (R := A.obj) _ _
    (toTensorSheafOverSource R A B a φ) x
    (isIso_stalkFunctor_map_toTensorSheafOverSource R A B a φ x) U hx t

section Kaehler

variable [DecidableEq (OrderDual (TopologicalSpace.OpenNhds x))]

/-- **The stalk of the tensor-differentials sheaf is the tensor-differentials module of the stalk
map.**  For a locally surjective morphism `φ : A ⟶ B` of sheaves of commutative rings with kernel
`I` and a morphism `a : R ⟶ A`, the stalk at `x` of `B ⊗[A] Ω[A/R]` is
`(Aₓ/Iₓ) ⊗[Aₓ] Ω[Aₓ/Rₓ]`, where `Iₓ` is the kernel of `Aₓ → Bₓ`. -/
def tensorDifferentialsSheafStalkLinearEquiv :
    letI := Stacks.RelativeDifferentialStalk.algebraStalk a.hom x
    ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
        (tensorDifferentialsSheaf (Opens.grothendieckTopology X) R A B a φ).val.presheaf x)
      ≃ₗ[ToType (TopCat.Presheaf.stalk A.obj x)]
      ((ToType (TopCat.Presheaf.stalk A.obj x) ⧸ stalkKernelIdeal φ.hom x)
        ⊗[ToType (TopCat.Presheaf.stalk A.obj x)]
        KaehlerDifferential (ToType (TopCat.Presheaf.stalk R.obj x))
          (ToType (TopCat.Presheaf.stalk A.obj x))) :=
  letI := Stacks.RelativeDifferentialStalk.algebraStalk a.hom x
  (tensorSheafStalkSheafifyLinearEquiv R A B a φ x).symm.trans
    (tensorPresheafStalkKaehlerLinearEquiv φ.hom a.hom x)

/-- **The identification carries universal differentials to universal differentials.**  The germ at
`x` of the local section `1 ⊗ d f` of `B ⊗[A] Ω[A/R]` goes to `1 ⊗ d (fₓ)`. -/
theorem tensorDifferentialsSheafStalkLinearEquiv_germ_tensorDifferential
    (U : Opens X) (hx : x ∈ U) (f : A.obj.obj (op U)) :
    letI := Stacks.RelativeDifferentialStalk.algebraStalk a.hom x
    tensorDifferentialsSheafStalkLinearEquiv R A B a φ x
        (TopCat.Presheaf.germ (C := AddCommGrpCat.{u})
          (tensorDifferentialsSheaf (Opens.grothendieckTopology X) R A B a φ).val.presheaf U x hx
          (tensorDifferential (Opens.grothendieckTopology X) R A B a φ (op U) f)) =
      (1 : ToType (TopCat.Presheaf.stalk A.obj x) ⧸ stalkKernelIdeal φ.hom x)
        ⊗ₜ[ToType (TopCat.Presheaf.stalk A.obj x)]
        KaehlerDifferential.D (ToType (TopCat.Presheaf.stalk R.obj x))
          (ToType (TopCat.Presheaf.stalk A.obj x))
          ((TopCat.Presheaf.germ A.obj U x hx).hom f) := by
  let := Stacks.RelativeDifferentialStalk.algebraStalk a.hom x
  have hE := tensorSheafStalkSheafifyLinearEquiv_germ R A B a φ x U hx
    ((1 : A.obj.obj (op U) ⧸ kernelIdeal φ.hom (op U)) ⊗ₜ[A.obj.obj (op U)]
      CommRingCat.KaehlerDifferential.d (f := a.hom.app (op U)) f)
  change tensorPresheafStalkKaehlerLinearEquiv φ.hom a.hom x
    ((tensorSheafStalkSheafifyLinearEquiv R A B a φ x).symm _) = _
  refine Eq.trans (congrArg (tensorPresheafStalkKaehlerLinearEquiv φ.hom a.hom x)
    ((LinearEquiv.symm_apply_eq _).mpr hE.symm)) ?_
  exact tensorPresheafStalkKaehlerLinearEquiv_germ_one_tmul_d φ.hom a.hom x U hx f

end Kaehler

/-! ### The stalk of the left-hand map of the conormal sequence -/

/-- The left-hand map of the conormal sequence, read as a morphism from the conormal sheaf to the
tensor-differentials sheaf. -/
def conormalSequenceFHom :
    conormalSheaf (Opens.grothendieckTopology X) A B φ ⟶
      tensorDifferentialsSheaf (Opens.grothendieckTopology X) R A B a φ :=
  (conormalSequence (Opens.grothendieckTopology X) R A B a φ).f

/-- The map induced on stalks at `x` by the left-hand map of the conormal sequence. -/
def conormalSequenceStalkMapF :
    ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
        (conormalSheaf (Opens.grothendieckTopology X) A B φ).val.presheaf x) →+
      ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
        (tensorDifferentialsSheaf (Opens.grothendieckTopology X) R A B a φ).val.presheaf x) :=
  ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
    ((PresheafOfModules.toPresheaf (Stacks.SheafOfModules.Tensor.ringSheaf B).obj).map
      (conormalSequenceFHom R A B a φ).val)).hom

/-- The stalk map carries the germ of a section to the germ of its image. -/
theorem conormalSequenceStalkMapF_germ (U : Opens X) (hx : x ∈ U)
    (c : (conormalSheaf (Opens.grothendieckTopology X) A B φ).val.obj (op U)) :
    conormalSequenceStalkMapF R A B a φ x
        (TopCat.Presheaf.germ (C := AddCommGrpCat.{u})
          (conormalSheaf (Opens.grothendieckTopology X) A B φ).val.presheaf U x hx c) =
      TopCat.Presheaf.germ (C := AddCommGrpCat.{u})
        (tensorDifferentialsSheaf (Opens.grothendieckTopology X) R A B a φ).val.presheaf U x hx
        (((conormalSequenceFHom R A B a φ).val.app (op U)) c) :=
  TopCat.Presheaf.stalkFunctor_map_germ_apply' U x hx
    ((PresheafOfModules.toPresheaf (Stacks.SheafOfModules.Tensor.ringSheaf B).obj).map
      (conormalSequenceFHom R A B a φ).val) c

section Kaehler

variable [DecidableEq (OrderDual (TopologicalSpace.OpenNhds x))]

/-- The stalk of the left-hand map of the conormal sequence sends the germ of the conormal class of
a section `y` of the kernel to `1 ⊗ d (yₓ)`. -/
theorem conormalSequenceStalkMapF_germ_conormalClass (U : Opens X) (hx : x ∈ U)
    (y : kernelIdeal φ.hom (op U)) :
    letI := Stacks.RelativeDifferentialStalk.algebraStalk a.hom x
    tensorDifferentialsSheafStalkLinearEquiv R A B a φ x
        (conormalSequenceStalkMapF R A B a φ x
          (TopCat.Presheaf.germ (C := AddCommGrpCat.{u})
            (conormalSheaf (Opens.grothendieckTopology X) A B φ).val.presheaf U x hx
            (conormalClass (Opens.grothendieckTopology X) R A B a φ (op U) y))) =
      (1 : ToType (TopCat.Presheaf.stalk A.obj x) ⧸ stalkKernelIdeal φ.hom x)
        ⊗ₜ[ToType (TopCat.Presheaf.stalk A.obj x)]
        KaehlerDifferential.D (ToType (TopCat.Presheaf.stalk R.obj x))
          (ToType (TopCat.Presheaf.stalk A.obj x))
          ((TopCat.Presheaf.germ A.obj U x hx).hom y) := by
  refine Eq.trans (congrArg (tensorDifferentialsSheafStalkLinearEquiv R A B a φ x)
    ((conormalSequenceStalkMapF_germ R A B a φ x U hx _).trans
      (congrArg (TopCat.Presheaf.germ (C := AddCommGrpCat.{u})
          (tensorDifferentialsSheaf (Opens.grothendieckTopology X) R A B a φ).val.presheaf
          U x hx).hom
        (conormalSequence_f_class (Opens.grothendieckTopology X) R A B a φ (op U) y)))) ?_
  exact tensorDifferentialsSheafStalkLinearEquiv_germ_tensorDifferential R A B a φ x U hx
    (y : A.obj.obj (op U))

/-- **The stalk of the left-hand map of the conormal sequence is the cotangent complex of the stalk
presentation.**  Under the identifications
`Stacks.Sites.Conormal.conormalSheafStalkLinearEquiv` and
`Stacks.Sites.Conormal.tensorDifferentialsSheafStalkLinearEquiv`, it is the map
`Iₓ/Iₓ² → (Aₓ/Iₓ) ⊗[Aₓ] Ω[Aₓ/Rₓ]` sending the conormal class of `y` to `1 ⊗ d y`, which is
`KaehlerDifferential.kerCotangentToTensor` for `Rₓ → Aₓ → Aₓ/Iₓ`.  Conormal classes generate, so
this determines the stalk map. -/
@[sga "6 0 4.3" "partial"]
theorem conormalSequenceStalkMapF_toCotangent (y : stalkKernelIdeal φ.hom x) :
    letI := Stacks.RelativeDifferentialStalk.algebraStalk a.hom x
    tensorDifferentialsSheafStalkLinearEquiv R A B a φ x
        (conormalSequenceStalkMapF R A B a φ x
          ((conormalSheafStalkLinearEquiv A B φ x).symm
            ((stalkKernelIdeal φ.hom x).toCotangent y))) =
      (1 : ToType (TopCat.Presheaf.stalk A.obj x) ⧸ stalkKernelIdeal φ.hom x)
        ⊗ₜ[ToType (TopCat.Presheaf.stalk A.obj x)]
        KaehlerDifferential.D (ToType (TopCat.Presheaf.stalk R.obj x))
          (ToType (TopCat.Presheaf.stalk A.obj x))
          (y : ToType (TopCat.Presheaf.stalk A.obj x)) := by
  let := Stacks.RelativeDifferentialStalk.algebraStalk a.hom x
  obtain ⟨U, hx, y₀, hy₀, hgy⟩ := exists_germ_eq_of_mem_stalkKernelIdeal φ.hom x
    (y : ToType (TopCat.Presheaf.stalk A.obj x)) y.2
  have hc : (conormalSheafStalkLinearEquiv A B φ x).symm
        ((stalkKernelIdeal φ.hom x).toCotangent y) =
      TopCat.Presheaf.germ (C := AddCommGrpCat.{u})
        (conormalSheaf (Opens.grothendieckTopology X) A B φ).val.presheaf U x hx
        (conormalClass (Opens.grothendieckTopology X) R A B a φ (op U) ⟨y₀, hy₀⟩) := by
    refine (LinearEquiv.symm_apply_eq _).mpr ?_
    refine Eq.symm ((conormalSheafStalkLinearEquiv_germ_conormalClass A B φ x R a U hx
      ⟨y₀, hy₀⟩).trans ?_)
    exact congrArg (stalkKernelIdeal φ.hom x).toCotangent (Subtype.ext hgy)
  refine Eq.trans (congrArg (fun z => tensorDifferentialsSheafStalkLinearEquiv R A B a φ x
    (conormalSequenceStalkMapF R A B a φ x z)) hc) ?_
  refine (conormalSequenceStalkMapF_germ_conormalClass R A B a φ x U hx ⟨y₀, hy₀⟩).trans ?_
  rw [hgy]

end Kaehler

end Sheaf

end Stacks.Sites.Conormal

end

end
