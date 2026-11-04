module

public import StacksFrontier.AlgebraicGeometry.Coherent.HomColimit.FirstDisplay
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.IdealProductTensor

/-!
# The surjection `Iⁿ ⊗_{𝒪_X} G ⟶ Iⁿ G` and the vanishing `Iⁿ · ker = 0`

Let `X` be a scheme, let `I` be a quasi-coherent sheaf of ideals on `X` and let `G` be an
`𝒪_X`-module.  Multiplication of sections is a morphism of `𝒪_X`-modules

`Iⁿ ⊗_{𝒪_X} G ⟶ G`,  `a ⊗ g ↦ a g`,

whose values lie in the subsheaf `Iⁿ G`, so it factors through a morphism

`Iⁿ ⊗_{𝒪_X} G ⟶ Iⁿ G`

which is an epimorphism when `G` is quasi-coherent.  Its kernel `𝒦` is annihilated by `Iⁿ`.

Both statements are steps of the proof of the first display of [Stacks, Tag 01YB]; the second is
the one the source records as "note that `Iⁿ 𝒦 = 0` (proof omitted)".

## Main definitions

* `smulToModule`: the morphism `A ⊗_{𝒪_X} G ⟶ G` attached to a morphism `φ : A ⟶ 𝒪_X`, sending
  a local pure tensor `a ⊗ g` to `φ(a) g`.
* `idealPowInclusion`: the inclusion `Iⁿ ⟶ 𝒪_X`, with its type pinned to `X.Modules`.
* `idealPowTensorToModule`: multiplication of sections `Iⁿ ⊗_{𝒪_X} G ⟶ G`.
* `idealPowTensorToSmul`: **the morphism `Iⁿ ⊗_{𝒪_X} G ⟶ Iⁿ G`.**

## Main results

* `smulToModule_app_toTensorSheafSection`: multiplication of sections on a local pure tensor.
* `epi_idealPowTensorToSmul`: **`Iⁿ ⊗_{𝒪_X} G ⟶ Iⁿ G` is an epimorphism** for `G`
  quasi-coherent.  Every section of `Iⁿ G` over an affine open is a finite sum `∑ aⱼ gⱼ` with
  `aⱼ ∈ I(V)ⁿ`, hence the image of a finite sum of pure tensors.
* `smul_eq_zero_of_idealPowTensorToSmul_eq_zero`: **`Iⁿ 𝒦 = 0`**, where `𝒦` is the kernel of
  `Iⁿ ⊗_{𝒪_X} G ⟶ Iⁿ G`: a section of `Iⁿ` times a section of the tensor product killed by the
  morphism is zero.
* `smul_toTensorSheafSection_idealPow`: the identity behind that vanishing, at the level of a
  local pure tensor: for `r` a section of `Iⁿ`, `r (x ⊗ b) = r ⊗ (x b)`.  Multiplication by a
  section of `Iⁿ` on the tensor product therefore factors through multiplication of sections,
  which is why it kills the kernel.
* `Submodule.exists_sum_smul_of_mem_smul`: an element of `I N` is a finite sum `∑ aⱼ gⱼ` with
  `aⱼ ∈ I` and `gⱼ ∈ N`.

## Implementation notes

**Multiplication of sections is the tensor product with the left unitor.**  `smulToModule φ G`
is `φ ⊗ 𝟙` followed by `AlgebraicGeometry.SheafOfModules.tensorSheafUnitLeftIso`, the left
unitor of the tensor product sheaf of Tag 01CA in the spelling whose action on local pure
tensors is `r ⊗ s ↦ r • s`.  The unitors of a monoidal structure obtained by localizing the
presheaf monoidal structure along sheafification have no such description.

**Sections of `𝒪_X` as an `𝒪_X`-module are not sections of `𝒪_X`.**  `Γ(𝒪_X, V)` carries no
multiplication and is not a scalar for `Γ(G, V)`: the two types agree definitionally but not at
the transparency of instance search.  Every statement below therefore passes the relevant
section of the structure sheaf as a separate `Γ(X, V)`-valued argument together with the
equation identifying it, as in
`Stacks.AlgebraicGeometry.IdealProduct.mulToStructure_app_toTensorSheafSection`.  For the same
reason a type ascription on a subtype's first projection does not make it a scalar — ascription
is erased when the two types are definitionally equal — so the sections of `Iⁿ` used as scalars
are introduced by `obtain` at the spelling `Γ(X, V)`.

**`Finset.smul_sum` is not available at these types.**  The instance `DistribSMul Γ(X, V)
Γ(M, V)` is not synthesized for `M` a tensor product sheaf; the sum is distributed instead
through `AlgebraicGeometry.Scheme.Modules.smul`, the ring homomorphism into the endomorphisms of
the sections, whose `map_sum` says the same thing.

## References

* [Stacks Project, Tag 01YB](https://stacks.math.columbia.edu/tag/01YB)
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace
open Stacks.AlgebraicGeometry.IdealPower
open Stacks.AlgebraicGeometry.IdealProduct
open Stacks.SheafOfModules.TensorUnit
open AlgebraicGeometry.SheafOfModules
  (tensorSheafUnitLeftIso tensorSheafUnitLeftIso_hom_toTensorSheafSection)

noncomputable section

universe u

/-- **An element of `I N` is a finite sum of multiples `aⱼ gⱼ` with `aⱼ ∈ I` and `gⱼ ∈ N`.** -/
public theorem Submodule.exists_sum_smul_of_mem_smul {R : Type*} [CommRing R] {M : Type*}
    [AddCommGroup M] [Module R M] {J : Ideal R} {N : Submodule R M} {x : M} (hx : x ∈ J • N) :
    ∃ (m : ℕ) (a : Fin m → R) (g : Fin m → M), (∀ j, a j ∈ J) ∧ x = ∑ j, a j • g j := by
  refine Submodule.smul_induction_on hx
    (fun r hr y _ ↦ ⟨1, fun _ ↦ r, fun _ ↦ y, fun _ ↦ hr, by simp⟩) ?_
  rintro u v ⟨m₁, a₁, g₁, ha₁, hu⟩ ⟨m₂, a₂, g₂, ha₂, hv⟩
  refine ⟨m₁ + m₂, Fin.append a₁ a₂, Fin.append g₁ g₂, fun j ↦ ?_, ?_⟩
  · exact Fin.addCases (fun i ↦ by simpa using ha₁ i) (fun i ↦ by simpa using ha₂ i) j
  · rw [Fin.sum_univ_add]
    simp [hu, hv]

namespace Stacks.AlgebraicGeometry.IdealPowerColimit

variable {X : Scheme.{u}}

/-! ### Multiplication of sections -/

/-- **Multiplication of sections.**  A morphism `φ : A ⟶ 𝒪_X` of `𝒪_X`-modules induces
`A ⊗_{𝒪_X} G ⟶ G`, sending a local pure tensor `a ⊗ g` to `φ(a) g`. -/
public noncomputable def smulToModule {A : X.Modules} (φ : A ⟶ structureModule X)
    (G : X.Modules) : tensorModules A G ⟶ G :=
  ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
    X.sheaf)).map (X := (A, G)) (Y := (structureModule X, G)) (φ, 𝟙 G)) ≫
    (tensorSheafUnitLeftIso X.toRingedSpace G).hom

/-- **Multiplication of sections, on a local pure tensor**: `smulToModule φ G` sends the image
of `a ⊗ g` in `A ⊗_{𝒪_X} G` to `φ(a) g`.

The value of `φ` is passed as a section `r` of the structure sheaf together with the equation
identifying it, because `Γ(𝒪_X, U)` is not a scalar for `Γ(G, U)` at the transparency of
instance search. -/
public theorem smulToModule_app_toTensorSheafSection {A : X.Modules}
    (φ : A ⟶ structureModule X) (G : X.Modules) (U : X.Opens) (a : Γ(A, U)) (g : Γ(G, U))
    (r : Γ(X, U)) (hr : φ.app U a = r) :
    (smulToModule φ G).app U
        (Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection X.toRingedSpace A G (op
        U)
          (a ⊗ₜ[X.presheaf.obj (op U)] g)) = r • g := by
  subst hr
  exact (congrArg (ConcreteCategory.hom
        ((tensorSheafUnitLeftIso X.toRingedSpace G).hom.val.app (op U)))
      (Stacks.SheafOfModules.TensorStalkRingedSpace.tensorSheafMap_app_toTensorSheafSection
      X.toRingedSpace A G
        (structureModule X) G φ (𝟙 G) U a g)).trans
    (tensorSheafUnitLeftIso_hom_toTensorSheafSection X.toRingedSpace G (op U) (φ.app U a) g)

/-! ### The morphism `Iⁿ ⊗_{𝒪_X} G ⟶ Iⁿ G` -/

/-- The inclusion `Iⁿ ⟶ 𝒪_X`, with its type pinned to `X.Modules`.

The ascription matters: `Scheme.Modules` is a `def`, so without it the application of this
morphism to sections is elaborated in `SheafOfModules`, where `Hom.app` does not exist. -/
public noncomputable abbrev idealPowInclusion (I : X.IdealSheafData) (n : ℕ) :
    idealPow I n ⟶ structureModule X :=
  (idealPowerMultiple I n (structureModule X)).ι

/-- Multiplication of sections of `Iⁿ` with sections of `G`, as a morphism
`Iⁿ ⊗_{𝒪_X} G ⟶ G`. -/
public noncomputable abbrev idealPowTensorToModule (I : X.IdealSheafData) (n : ℕ)
    (G : X.Modules) : tensorModules (idealPow I n) G ⟶ G :=
  smulToModule (idealPowInclusion I n) G

/-- Multiplication of sections on a finite sum of local pure tensors `xⱼ ⊗ bⱼ`, where `sⱼ` is
the value of `xⱼ` in the structure sheaf. -/
private theorem idealPowTensorToModule_app_sum (I : X.IdealSheafData) (n : ℕ) (G : X.Modules)
    (V : X.Opens) {m : ℕ} (x : Fin m → Γ(idealPow I n, V)) (b : Fin m → Γ(G, V))
    (s : Fin m → Γ(X, V)) (hs : ∀ j, (idealPowInclusion I n).app V (x j) = s j) :
    (idealPowTensorToModule I n G).app V
      (∑ j, Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection X.toRingedSpace
        (idealPow I n) G (op V) (x j ⊗ₜ[X.presheaf.obj (op V)] b j)) = ∑ j, s j • b j :=
  (map_sum _ _ _).trans <| Finset.sum_congr rfl fun j _ ↦
    smulToModule_app_toTensorSheafSection _ G V (x j) (b j) (s j) (hs j)

/-- **Multiplication of sections of `Iⁿ` with sections of `G` takes values in `Iⁿ G`.**  The
containment is checked on an affine open neighbourhood of each point, where a section of the
tensor product is a finite sum of pure tensors and each summand `a g` lies in `Iⁿ G` by
`Stacks.AlgebraicGeometry.IdealPowerColimit.smul_mem_idealPowerMultiple`. -/
public theorem exists_mem_idealPowerMultiple_idealPowTensor (I : X.IdealSheafData) (n : ℕ)
    (G : X.Modules) (W : X.Opens) (t : Γ(tensorModules (idealPow I n) G, W)) (p : X)
    (hp : p ∈ W) :
    ∃ (V : X.Opens) (hV : V ≤ W), p ∈ V ∧
      (idealPowTensorToModule I n G).app V
          ((tensorModules (idealPow I n) G).presheaf.map (homOfLE hV).op t) ∈
        (idealPowerMultiple I n G).toSubmodule.obj (op V) := by
  obtain ⟨V, hV, hpV, m, a, b, heq⟩ :=
    exists_affineOpen_sum_toTensorSheafSection (idealPow I n) G W t p hp
  refine ⟨V.1, hV, hpV, ?_⟩
  refine Eq.subst (motive := fun z ↦ z ∈ (idealPowerMultiple I n G).toSubmodule.obj (op V.1))
    ((congrArg (ConcreteCategory.hom ((idealPowTensorToModule I n G).app V.1)) heq).trans
      (idealPowTensorToModule_app_sum I n G V.1 a b (fun j ↦ (a j).1) fun _ ↦ rfl)).symm ?_
  exact Submodule.sum_mem _ fun j _ ↦ smul_mem_idealPowerMultiple I n G _ (a j).2 (b j)

/-- **The morphism `Iⁿ ⊗_{𝒪_X} G ⟶ Iⁿ G`**, the factorization of multiplication of sections
through the subsheaf `Iⁿ G` of `G`. -/
public noncomputable def idealPowTensorToSmul (I : X.IdealSheafData) (n : ℕ) (G : X.Modules) :
    tensorModules (idealPow I n) G ⟶ idealPowSmul I n G :=
  factorThruOfLocalMem (idealPowerMultiple I n G) (idealPowTensorToModule I n G)
    (exists_mem_idealPowerMultiple_idealPowTensor I n G)

/-- The morphism `Iⁿ ⊗_{𝒪_X} G ⟶ Iⁿ G` followed by the inclusion of `Iⁿ G` into `G` is
multiplication of sections. -/
@[reassoc (attr := simp)]
public theorem idealPowTensorToSmul_ι (I : X.IdealSheafData) (n : ℕ) (G : X.Modules) :
    idealPowTensorToSmul I n G ≫ (idealPowerMultiple I n G).ι =
      idealPowTensorToModule I n G :=
  factorThruOfLocalMem_ι _ _ _

/-- The morphism `Iⁿ ⊗_{𝒪_X} G ⟶ Iⁿ G` does not change the value of a section: as a section of
`G` it is the product of the two factors. -/
public theorem val_idealPowTensorToSmul_app (I : X.IdealSheafData) (n : ℕ) (G : X.Modules)
    (V : X.Opens) (z : Γ(tensorModules (idealPow I n) G, V)) :
    (((idealPowTensorToSmul I n G).app V z).1 : Γ(G, V)) =
      (idealPowTensorToModule I n G).app V z := rfl

/-! ### The morphism is an epimorphism -/

/-- **A section of `Iⁿ G` over an affine open is a finite sum `∑ aⱼ gⱼ` with `aⱼ ∈ I(V)ⁿ`.**
For a quasi-coherent `G` the sections of `Iⁿ G` over an affine open `V` are `I(V)ⁿ Γ(G, V)`. -/
public theorem exists_sum_smul_of_mem_idealPowerMultiple (I : X.IdealSheafData) (n : ℕ)
    (G : X.Modules) [G.IsQuasicoherent] (V : X.affineOpens) {x : Γ(G, V.1)}
    (hx : x ∈ (idealPowerMultiple I n G).toSubmodule.obj (op V.1)) :
    ∃ (m : ℕ) (a : Fin m → Γ(X, V.1)) (g : Fin m → Γ(G, V.1)),
      (∀ j, a j ∈ (I.ideal V ^ n : Ideal Γ(X, V.1))) ∧ x = ∑ j, a j • g j :=
  Submodule.exists_sum_smul_of_mem_smul ((idealPowerMultiple_obj_affineOpen I n G V).le hx)

/-- **The morphism `Iⁿ ⊗_{𝒪_X} G ⟶ Iⁿ G` is an epimorphism**, for `G` quasi-coherent.  Every
section of `Iⁿ G` over an affine open is a finite sum `∑ aⱼ gⱼ` with `aⱼ ∈ I(V)ⁿ`, hence the
image of the corresponding finite sum of pure tensors. -/
public theorem epi_idealPowTensorToSmul (I : X.IdealSheafData) (n : ℕ) (G : X.Modules)
    [G.IsQuasicoherent] : Epi (idealPowTensorToSmul I n G) := by
  have hepi : @Epi (SheafOfModules X.ringCatSheaf) _ _ _ (idealPowTensorToSmul I n G) := by
    refine Stacks.SheafOfModules.StalkEpiMono.epi_of_exists_sections _ fun W t p hp ↦ ?_
    obtain ⟨-, ⟨V, hVaff, rfl⟩, hpV, hVW⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (show p ∈ (W : Set X) from hp) W.isOpen
    obtain ⟨m, a, g, ha, hsum⟩ :=
      exists_sum_smul_of_mem_idealPowerMultiple I n G ⟨V, hVaff⟩
        ((idealPowSmul I n G).val.map (homOfLE hVW).op t).2
    refine ⟨V, hVW, hpV, ∑ j, Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection
    X.toRingedSpace
      (idealPow I n) G (op V)
      (⟨a j, (obj_idealPow_affineOpen I n ⟨V, hVaff⟩).ge (ha j)⟩ ⊗ₜ[X.presheaf.obj (op V)]
        g j), Subtype.ext ?_⟩
    exact (val_idealPowTensorToSmul_app I n G V _).trans <|
      (idealPowTensorToModule_app_sum I n G V _ g a fun _ ↦ rfl).trans hsum.symm
  exact ⟨fun g₁ g₂ h ↦ hepi.left_cancellation g₁ g₂ h⟩

/-! ### The kernel is annihilated by `Iⁿ` -/

/-- **Two sections of `Iⁿ` commute as scalars on each other.**  Both values are passed as
sections of the structure sheaf together with the equations identifying them, since the
sections of `Iⁿ` are not themselves scalars. -/
public theorem smul_comm_idealPow (I : X.IdealSheafData) (n : ℕ) {W : X.Opens}
    (y z : Γ(idealPow I n, W)) {r s : Γ(X, W)} (hr : (idealPowInclusion I n).app W y = r)
    (hs : (idealPowInclusion I n).app W z = s) :
    r • z = s • y := by
  have h : (idealPowInclusion I n).app W (r • z)
      = (idealPowInclusion I n).app W (s • y) := by
    rw [Scheme.Modules.Hom.app_smul, Scheme.Modules.Hom.app_smul, hr, hs]
    exact mul_comm r s
  exact Subtype.ext h

/-- **A scalar passes into the left factor of a local pure tensor** of the tensor product sheaf:
the map on sections is the sheafification unit, which is linear, and in the presheaf tensor
product `r (a ⊗ b) = (r a) ⊗ b`. -/
public theorem smul_toTensorSheafSection (A G : X.Modules) (V : X.Opens) (r : Γ(X, V))
    (a : Γ(A, V)) (b : Γ(G, V)) :
    HSMul.hSMul (α := Γ(X, V)) (β := Γ(tensorModules A G, V)) r
        (Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection X.toRingedSpace A G
          (op V) (a ⊗ₜ[X.presheaf.obj (op V)] b))
      = Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection X.toRingedSpace A G (op V)
          ((r • a) ⊗ₜ[X.presheaf.obj (op V)] b) :=
  (map_smul ((Stacks.SheafOfModules.TensorStalkRingedSpace.sheafifyUnit X.toRingedSpace
      ((PresheafOfModules.tensorObj (O := (X.toRingedSpace).presheaf) (A.val) (G.val)))).app
      (op V)).hom r
      (a ⊗ₜ[X.presheaf.obj (op V)] b)).symm.trans
    (congrArg (Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection X.toRingedSpace A G
    (op V))
      (TensorProduct.smul_tmul' r a b))

/-- **Multiplication by a section of `Iⁿ` on a local pure tensor of `Iⁿ ⊗_{𝒪_X} G` factors
through multiplication of sections**: for `y` a section of `Iⁿ` with value `r`, and `x` a
section of `Iⁿ` with value `s`,

`r (x ⊗ b) = y ⊗ (s b)`.

This is the reason the kernel of `Iⁿ ⊗_{𝒪_X} G ⟶ Iⁿ G` is annihilated by `Iⁿ`: the right-hand
side only depends on the image of `x ⊗ b` under multiplication of sections. -/
public theorem smul_toTensorSheafSection_idealPow (I : X.IdealSheafData) (n : ℕ)
    (G : X.Modules) {W : X.Opens} (y : Γ(idealPow I n, W)) {r : Γ(X, W)}
    (hr : (idealPowInclusion I n).app W y = r)
    (x : Γ(idealPow I n, W)) {s : Γ(X, W)} (hs : (idealPowInclusion I n).app W x = s)
    (b : Γ(G, W)) :
    HSMul.hSMul (α := Γ(X, W)) (β := Γ(tensorModules (idealPow I n) G, W)) r
        (Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection X.toRingedSpace
          (idealPow I n) G (op W) (x ⊗ₜ[X.presheaf.obj (op W)] b))
      = Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection X.toRingedSpace (idealPow
      I n) G (op W)
          (y ⊗ₜ[X.presheaf.obj (op W)] (s • b)) := by
  refine (smul_toTensorSheafSection (idealPow I n) G W r x b).trans ?_
  refine congrArg (Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection X.toRingedSpace
  (idealPow I n) G (op W))
    ?_
  refine (congrArg (fun w : Γ(idealPow I n, W) ↦ w ⊗ₜ[X.presheaf.obj (op W)] b)
    (smul_comm_idealPow I n y x hr hs)).trans ?_
  exact (TensorProduct.smul_tmul' s y b).symm.trans (TensorProduct.smul_tmul s y b)

/-- **A section of `Iⁿ` annihilates every section of `Iⁿ ⊗_{𝒪_X} G` killed by multiplication of
sections.**

The equality is local, and on an open where the section of the tensor product is a finite sum
of pure tensors `∑ xⱼ ⊗ bⱼ` the scalar passes to the right-hand factors by
`smul_toTensorSheafSection_idealPow`, turning the product into the single pure tensor
`a ⊗ ∑ xⱼ bⱼ`, whose right-hand factor is the image of the section under multiplication of
sections and hence zero. -/
public theorem smul_eq_zero_of_idealPowTensorToModule_eq_zero (I : X.IdealSheafData) (n : ℕ)
    (G : X.Modules) {V : X.Opens} {a : Γ(X, V)}
    (ha : a ∈ (idealPowerMultiple I n (structureModule X)).toSubmodule.obj (op V))
    {t : Γ(tensorModules (idealPow I n) G, V)}
    (ht : (idealPowTensorToModule I n G).app V t = 0) :
    a • t = 0 := by
  refine eq_zero_of_locally_zero _ fun p hp ↦ ?_
  obtain ⟨W, hWV, hpW, m, x, b, heq⟩ :=
    exists_affineOpen_sum_toTensorSheafSection (idealPow I n) G V t p hp
  refine ⟨W.1, hWV, hpW, ?_⟩
  obtain ⟨s, hs⟩ : ∃ s : Fin m → Γ(X, W.1),
      ∀ j, (idealPowInclusion I n).app W.1 (x j) = s j :=
    ⟨fun j ↦ (idealPowInclusion I n).app W.1 (x j), fun _ ↦ rfl⟩
  obtain ⟨aW, haW⟩ : ∃ aW : Γ(idealPow I n, W.1),
      (idealPowInclusion I n).app W.1 aW = X.presheaf.map (homOfLE hWV).op a :=
    ⟨⟨X.presheaf.map (homOfLE hWV).op a,
      (idealPowerMultiple I n (structureModule X)).toSubmodule.map_mem (homOfLE hWV).op ha⟩,
      rfl⟩
  have h1 : (idealPowTensorToModule I n G).app W.1
      ((tensorModules (idealPow I n) G).presheaf.map (homOfLE hWV).op t) = 0 := by
    rw [← app_naturality (idealPowTensorToModule I n G) hWV t, ht, map_zero]
  have hzero : ∑ j, s j • b j = (0 : Γ(G, W.1)) := by
    refine (idealPowTensorToModule_app_sum I n G W.1 x b s hs).symm.trans ?_
    exact (congrArg (ConcreteCategory.hom ((idealPowTensorToModule I n G).app W.1))
      heq.symm).trans h1
  refine (Scheme.Modules.map_smul _ _ _ _).trans ?_
  refine (congrArg (fun u : Γ(tensorModules (idealPow I n) G, W.1) ↦
    X.presheaf.map (homOfLE hWV).op a • u) heq).trans ?_
  refine (map_sum (((tensorModules (idealPow I n) G).smul (U := W.1)
    (X.presheaf.map (homOfLE hWV).op a)).hom) _ Finset.univ).trans ?_
  refine (Finset.sum_congr rfl fun j _ ↦
    smul_toTensorSheafSection_idealPow I n G aW haW (x j) (hs j) (b j)).trans ?_
  refine (map_sum ((Stacks.SheafOfModules.TensorStalkRingedSpace.sheafifyUnit X.toRingedSpace
      ((PresheafOfModules.tensorObj (O := (X.toRingedSpace).presheaf) ((idealPow I
      n).val) (G.val)))).app
        (op W.1)).hom _ Finset.univ).symm.trans ?_
  refine (congrArg (Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection
  X.toRingedSpace (idealPow I n) G
    (op W.1)) (TensorProduct.tmul_sum _ _ _).symm).trans ?_
  refine (congrArg (Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection
  X.toRingedSpace (idealPow I n) G
    (op W.1)) ((congrArg (fun v : Γ(G, W.1) ↦ aW ⊗ₜ[X.presheaf.obj (op W.1)] v) hzero).trans
      (TensorProduct.tmul_zero _ aW))).trans ?_
  exact map_zero _

/-- **`Iⁿ 𝒦 = 0`, where `𝒦` is the kernel of `Iⁿ ⊗_{𝒪_X} G ⟶ Iⁿ G`.**  A section of `Iⁿ` times
a section of the tensor product annihilated by that morphism is zero.

This is the step [Stacks, Tag 01YB] records as "note that `Iⁿ 𝒦 = 0` (proof omitted)". -/
public theorem smul_eq_zero_of_idealPowTensorToSmul_eq_zero (I : X.IdealSheafData) (n : ℕ)
    (G : X.Modules) {V : X.Opens} {a : Γ(X, V)}
    (ha : a ∈ (idealPowerMultiple I n (structureModule X)).toSubmodule.obj (op V))
    {t : Γ(tensorModules (idealPow I n) G, V)}
    (ht : (idealPowTensorToSmul I n G).app V t = 0) :
    a • t = 0 := by
  refine smul_eq_zero_of_idealPowTensorToModule_eq_zero I n G ha ?_
  refine (val_idealPowTensorToSmul_app I n G V t).symm.trans ?_
  exact congrArg (fun u : Γ(idealPowSmul I n G, V) ↦ (u.1 : Γ(G, V))) ht

end Stacks.AlgebraicGeometry.IdealPowerColimit

end

end
