module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.ClosedImmersionPositiveCharacteristic
public import
  StacksFrontier.AlgebraicGeometry.FundamentalGroup.LocalConnectedness.ClosedPointExactSequence
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.LocalConnectedness.FinitePointChain
public import
  StacksFrontier.AlgebraicGeometry.FundamentalGroup.LocalConnectedness.PuncturedSpectrumDescent
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.SpecializationMap

/-!
# The kernel of `π₁(U) ⟶ π₁(X)` after removing finitely many closed points

Let `X` be a connected scheme, let `x₀, …, xₙ₋₁ ∈ X` be pairwise distinct closed points and let
`U = X ∖ {x₀, …, xₙ₋₁}`, assumed connected and retrocompact in `X`. Let `Aᵢˢʰ` be a strict
henselization of `𝒪_{X,xᵢ}` and let `Uᵢˢʰ` be its punctured spectrum, assumed connected for every
`i`. Then the map `π₁(U, ū) ⟶ π₁(X, ū)` is surjective, and its kernel is the smallest closed
normal subgroup of `π₁(U, ū)` containing the images of the maps `π₁(Uᵢˢʰ) ⟶ π₁(U)`.

## Main definitions

* `AlgebraicGeometry.chainStep`: the `i`-th step `X ∖ {xⱼ : i ≤ j} ⟶ X ∖ {xⱼ : i + 1 ≤ j}` of the
  chain of opens from `U` to `X`.
* `AlgebraicGeometry.chainRemovedPoint`: the point `xᵢ` removed by the `i`-th step.
* `AlgebraicGeometry.chainStepIso`: the `i`-th stage of the chain, identified with the complement
  of the removed point in the next stage.
* `AlgebraicGeometry.chainLocalPunctured`: `Uᵢˢʰ`, the preimage of the complement of `xᵢ` in
  `Spec Aᵢˢʰ`.
* `AlgebraicGeometry.chainLocalLift`: the factorisation `Uᵢˢʰ ⟶ U` of the morphism `Uᵢˢʰ ⟶ X`.

## Main results

* `AlgebraicGeometry.surjective_and_ker_etaleFundamentalGroupMap_of_finite_isClosed_compl`: the
  map `π₁(U, ū) ⟶ π₁(X, ū)` is surjective, and its kernel is the smallest closed normal subgroup
  containing the images of the maps `π₁(Uᵢˢʰ) ⟶ π₁(U)`.
* `AlgebraicGeometry.ker_etaleFundamentalGroupMap_eq_closedNormalClosure_biUnion_range`: the
  description of the kernel alone.
* `AlgebraicGeometry.isExactSequence_etaleFundamentalGroupMap_puncturedOpen_of_quasiCompact`: the
  exact sequence `π₁(Vˢʰ) → π₁(Y ∖ {y}) → π₁(Y) → 1` at a closed point `y` of a connected scheme
  `Y` with connected and retrocompact complement.
* `AlgebraicGeometry.ker_etaleFundamentalGroupMap_of_iso`: transport of a kernel presented as a
  closed normal closure along an isomorphism of schemes and a change of base point.
* `AlgebraicGeometry.exists_fiberFunctorIso_chainGroupMap_comp`: the composite along a chain of a
  map from a connected scheme into its bottom stage, after a change of base point.
* `AlgebraicGeometry.injective_etaleFundamentalGroupMap_of_isIso`,
  `AlgebraicGeometry.surjective_etaleFundamentalGroupMap_of_isIso`: an isomorphism of connected
  schemes is bijective on étale fundamental groups.
* `Stacks.FundamentalGroup.ker_eq_closedNormalClosure_image`: a presentation of a kernel as a
  smallest closed normal subgroup descends along a surjective closed continuous homomorphism.

## Implementation notes

The removed points are assumed pairwise distinct (`hinj`); the source writes `x₁, …, xₙ` and does
not say so. Deleting a repetition changes neither `U` nor the union of the local images, but a
repeated point is removed by no step of the chain.

The connectedness of `Uᵢˢʰ`, hypothesis (2) of the source, is stated (`hconn`) at the stalks of
the stages of the chain at the points they remove rather than at the stalks of `X`. An open
immersion is an isomorphism on stalks, so the two forms agree.

The conclusion holds for every choice of geometric points `ūᵢ` of `Uᵢˢʰ` and of comparisons `s i`
of the fibre functors of `U` at the image of `ūᵢ` and at `ū`; the closed normal closure does not
depend on that choice, since two choices differ by an inner automorphism.

## References

* [Stacks Project, Tag 0BSC](https://stacks.math.columbia.edu/tag/0BSC)
* [Stacks Project, Tag 0BSB](https://stacks.math.columbia.edu/tag/0BSB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits IsLocalRing Stacks.Divisors
open Stacks.FundamentalGroup AlgebraicGeometry.GlueingNearPoint

universe u

namespace Stacks.FundamentalGroup

section Groups

variable {G₂ G₁ G₀ : Type*}
  [Group G₂] [TopologicalSpace G₂] [IsTopologicalGroup G₂]
  [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁]
  [Group G₀] [TopologicalSpace G₀]

/-- A subgroup of a topological group, included in it as a continuous homomorphism. -/
def subtypeContinuousMonoidHom (H : Subgroup G₂) : H →ₜ* G₂ where
  toMonoidHom := H.subtype
  continuous_toFun := continuous_subtype_val

omit [IsTopologicalGroup G₂] in
/-- The range of the inclusion of a subgroup is the subgroup. -/
theorem range_subtypeContinuousMonoidHom (H : Subgroup G₂) :
    Set.range (subtypeContinuousMonoidHom H) = (H : Set G₂) := Subtype.range_coe

/-- The image of a smallest closed normal subgroup containing a set, under a surjective closed
continuous homomorphism, is the smallest closed normal subgroup containing the image of the
set. -/
theorem map_closedNormalClosure (φ : G₂ →ₜ* G₁) (hsurj : Function.Surjective φ)
    (hclosedmap : IsClosedMap φ) (T : Set G₂) :
    Subgroup.map φ.toMonoidHom (Subgroup.normalClosure T).topologicalClosure =
      (Subgroup.normalClosure (φ '' T)).topologicalClosure := by
  refine SetLike.coe_injective ?_
  rw [show (⇑φ '' T) = (⇑φ.toMonoidHom '' T) from rfl, Subgroup.coe_map,
    Subgroup.topologicalClosure_coe, Subgroup.topologicalClosure_coe,
    ← Subgroup.map_normalClosure T φ.toMonoidHom hsurj, Subgroup.coe_map]
  refine Set.Subset.antisymm ?_ ?_
  · exact (map_continuous φ).continuousOn.image_closure
  · exact closure_minimal (Set.image_mono subset_closure) (hclosedmap _ isClosed_closure)

/-- **Descending a presentation of a kernel along a surjection.** If `φ` is a surjective closed
continuous homomorphism and the kernel of `ψ ∘ φ` is the smallest closed normal subgroup
containing `T`, then the kernel of `ψ` is the smallest closed normal subgroup containing the
image of `T`. -/
theorem ker_eq_closedNormalClosure_image (φ : G₂ →ₜ* G₁) (ψ : G₁ →ₜ* G₀)
    (hsurj : Function.Surjective φ) (hclosedmap : IsClosedMap φ) {T : Set G₂}
    (h : MonoidHom.ker (ψ.toMonoidHom.comp φ.toMonoidHom) =
      (Subgroup.normalClosure T).topologicalClosure) :
    MonoidHom.ker ψ.toMonoidHom = (Subgroup.normalClosure (φ '' T)).topologicalClosure := by
  rw [← map_closedNormalClosure φ hsurj hclosedmap T, ← h, ← MonoidHom.comap_ker,
    Subgroup.map_comap_eq_self_of_surjective hsurj]

omit [IsTopologicalGroup G₂] [IsTopologicalGroup G₁] in
/-- The kernel of a continuous homomorphism into a Hausdorff group is closed. -/
theorem isClosed_ker (f : G₂ →ₜ* G₁) [T2Space G₁] :
    IsClosed ((MonoidHom.ker f.toMonoidHom : Subgroup G₂) : Set G₂) :=
  isClosed_singleton.preimage (map_continuous f)

/-- A closed normal subgroup is the smallest closed normal subgroup containing itself. -/
theorem closedNormalClosure_coe_eq_self (K : Subgroup G₂) [K.Normal]
    (hclosed : IsClosed (K : Set G₂)) :
    (Subgroup.normalClosure (K : Set G₂)).topologicalClosure = K := by
  rw [Subgroup.normalClosure_eq_self]
  exact SetLike.coe_injective (by rw [Subgroup.topologicalClosure_coe, hclosed.closure_eq])

end Groups

end Stacks.FundamentalGroup

namespace AlgebraicGeometry

/-! ### Isomorphisms and a change of base point -/

/-- A change of geometric base point, as a continuous homomorphism of étale fundamental
groups. -/
def etaleFundamentalGroupChange {V : Scheme.{u}} [ConnectedSpace V] {q v : GeometricPoint V}
    (t : finiteEtaleFiberFunctor q ≅ finiteEtaleFiberFunctor v) :
    EtaleFundamentalGroup V q →ₜ* EtaleFundamentalGroup V v where
  toMonoidHom := (etaleFundamentalGroupMulEquiv t).toMonoidHom
  continuous_toFun := continuous_etaleFundamentalGroupMulEquiv t

/-- An isomorphism of connected schemes is surjective on étale fundamental groups. -/
theorem surjective_etaleFundamentalGroupMap_of_isIso {V P : Scheme.{u}} [ConnectedSpace V]
    [ConnectedSpace P] (g : V ⟶ P) [IsIso g] (p : GeometricPoint V) :
    Function.Surjective (etaleFundamentalGroupMap g p) := by
  have hsurj : Function.Surjective g.base := g.surjective
  exact surjective_etaleFundamentalGroupMap_of_fullyFaithful g p
    (fullyFaithful_finiteEtaleBaseChange_of_quasiCompact_of_isClosed_compl g
      (fun w hw ↦ absurd (hsurj w) hw) (fun w hw ↦ absurd (hsurj w) hw))

/-- An isomorphism of connected schemes is injective on étale fundamental groups. -/
theorem injective_etaleFundamentalGroupMap_of_isIso {Z Y : Scheme.{u}} [ConnectedSpace Z]
    [ConnectedSpace Y] (g : Z ⟶ Y) [IsIso g] (z : GeometricPoint Z) :
    Function.Injective (etaleFundamentalGroupMap g z) := by
  refine injective_etaleFundamentalGroupMap_of_forall_exists_mono g z fun V ↦ ?_
  have hfe : finiteEtale (V.hom ≫ g) :=
    finiteEtale.comp_mem _ _ V.prop (MorphismProperty.of_isIso _ g)
  refine ⟨MorphismProperty.Over.mk ⊤ (V.hom ≫ g) hfe,
    MorphismProperty.Over.homMk
      (pullback.lift (CategoryStruct.id V.left) V.hom (Category.id_comp (V.hom ≫ g)))
      (pullback.lift_snd _ _ _) trivial, ?_⟩
  have hsplit : (pullback.lift (CategoryStruct.id V.left) V.hom
      (Category.id_comp (V.hom ≫ g))) ≫ pullback.fst (V.hom ≫ g) g =
      CategoryStruct.id V.left := pullback.lift_fst _ _ _
  exact (IsSplitMono.mk' ⟨_, hsplit⟩).mono

/-- Composing with an isomorphism does not change the kernel of the induced map of étale
fundamental groups. -/
theorem ker_etaleFundamentalGroupMap_comp_isIso {A B C : Scheme.{u}} [ConnectedSpace A]
    [ConnectedSpace B] [ConnectedSpace C] (a : A ⟶ B) (b : B ⟶ C) [IsIso b]
    (p : GeometricPoint A) :
    MonoidHom.ker (etaleFundamentalGroupMap (a ≫ b) p).toMonoidHom =
      MonoidHom.ker (etaleFundamentalGroupMap a p).toMonoidHom := by
  ext σ
  show etaleFundamentalGroupMap (a ≫ b) p σ = 1 ↔ etaleFundamentalGroupMap a p σ = 1
  rw [← map_eq_one_iff _ (etaleFundamentalGroupMulEquiv (fiberFunctorMapCompIso a b p)).injective,
    etaleFundamentalGroupMulEquiv_mapCompIso]
  exact map_eq_one_iff _ (injective_etaleFundamentalGroupMap_of_isIso b (p.map a))

/-- **Transport of a kernel presentation along an isomorphism and a change of base point.** Let
`r : Z ⟶ P`, let `θ : V ≅ P` and let `sV : V ⟶ W`. If the kernel of the map induced by
`θ⁻¹ ∘ sV` at `z ∘ r` is the smallest closed normal subgroup containing the image of `π₁(Z, z)`,
then the kernel of the map induced by `sV` at any base point `v` of `V` is the smallest closed
normal subgroup containing the image of `π₁(Z, z)` transported to `v`. -/
theorem ker_etaleFundamentalGroupMap_of_iso
    {Z P V W : Scheme.{u}} [ConnectedSpace Z] [ConnectedSpace P] [ConnectedSpace V]
    [ConnectedSpace W] (r : Z ⟶ P) (θ : V ≅ P) (sV : V ⟶ W) (z : GeometricPoint Z)
    (v : GeometricPoint V)
    (t : finiteEtaleFiberFunctor ((z.map r).map θ.inv) ≅ finiteEtaleFiberFunctor v)
    (hker : MonoidHom.ker (etaleFundamentalGroupMap (θ.inv ≫ sV) (z.map r)).toMonoidHom =
      (Subgroup.normalClosure
        (Set.range (etaleFundamentalGroupMap r z))).topologicalClosure) :
    MonoidHom.ker (etaleFundamentalGroupMap sV v).toMonoidHom =
      (Subgroup.normalClosure (Set.range
        (((etaleFundamentalGroupChange t).comp
          ((etaleFundamentalGroupMap θ.inv (z.map r)).comp
            (etaleFundamentalGroupMap r z)))))).topologicalClosure := by
  have _ := compactSpace_etaleFundamentalGroup P (z.map r)
  have _ := compactSpace_etaleFundamentalGroup V ((z.map r).map θ.inv)
  have _ := t2Space_etaleFundamentalGroup V ((z.map r).map θ.inv)
  have _ := t2Space_etaleFundamentalGroup V v
  have key : ∀ σ : EtaleFundamentalGroup P (z.map r),
      etaleFundamentalGroupMap sV ((z.map r).map θ.inv)
          (etaleFundamentalGroupMap θ.inv (z.map r) σ) = 1 ↔
        etaleFundamentalGroupMap (θ.inv ≫ sV) (z.map r) σ = 1 := by
    intro σ
    rw [← etaleFundamentalGroupMulEquiv_mapCompIso θ.inv sV (z.map r) σ]
    exact map_eq_one_iff _ (etaleFundamentalGroupMulEquiv
      (fiberFunctorMapCompIso θ.inv sV (z.map r))).injective
  have hA : MonoidHom.ker
      ((etaleFundamentalGroupMap sV ((z.map r).map θ.inv)).toMonoidHom.comp
        (etaleFundamentalGroupMap θ.inv (z.map r)).toMonoidHom) =
      (Subgroup.normalClosure (Set.range (etaleFundamentalGroupMap r z))).topologicalClosure := by
    rw [← hker]
    ext σ
    simp only [MonoidHom.mem_ker, MonoidHom.coe_comp, Function.comp_apply,
      ContinuousMonoidHom.coe_toMonoidHom]
    exact key σ
  have hB : MonoidHom.ker (etaleFundamentalGroupMap sV ((z.map r).map θ.inv)).toMonoidHom =
      (Subgroup.normalClosure (etaleFundamentalGroupMap θ.inv (z.map r) ''
        Set.range (etaleFundamentalGroupMap r z))).topologicalClosure :=
    Stacks.FundamentalGroup.ker_eq_closedNormalClosure_image
      (etaleFundamentalGroupMap θ.inv (z.map r))
      (etaleFundamentalGroupMap sV ((z.map r).map θ.inv))
      (surjective_etaleFundamentalGroupMap_of_isIso θ.inv (z.map r))
      (map_continuous (etaleFundamentalGroupMap θ.inv (z.map r))).isClosedMap hA
  have hC : MonoidHom.ker ((etaleFundamentalGroupMap sV v).toMonoidHom.comp
        (etaleFundamentalGroupChange t).toMonoidHom) =
      MonoidHom.ker (etaleFundamentalGroupMap sV ((z.map r).map θ.inv)).toMonoidHom := by
    ext σ
    have hint : etaleFundamentalGroupMap sV v (etaleFundamentalGroupChange t σ)
        = etaleFundamentalGroupMulEquiv (fiberFunctorTransportIso sV t)
            (etaleFundamentalGroupMap sV ((z.map r).map θ.inv) σ) :=
      (etaleFundamentalGroupMulEquiv_transportIso sV t σ).symm
    show etaleFundamentalGroupMap sV v (etaleFundamentalGroupChange t σ) = 1 ↔
      etaleFundamentalGroupMap sV ((z.map r).map θ.inv) σ = 1
    rw [hint]
    exact map_eq_one_iff _ (etaleFundamentalGroupMulEquiv
      (fiberFunctorTransportIso sV t)).injective
  have hD := Stacks.FundamentalGroup.ker_eq_closedNormalClosure_image
    (etaleFundamentalGroupChange t) (etaleFundamentalGroupMap sV v)
    (etaleFundamentalGroupMulEquiv t).surjective
    (map_continuous (etaleFundamentalGroupChange t)).isClosedMap (hC.trans hB)
  rw [hD]
  congr 1
  rw [← Set.range_comp, ← Set.range_comp]
  rfl

/-! ### The composite along a chain, after a change of base point -/

variable {B : ℕ → Scheme.{u}} [∀ j, ConnectedSpace (B j)]

/-- **The composite along a chain of a map coming from below.** Let `d` be a chain of connected
schemes, `u` a geometric point of `B 0`, and `k : Z ⟶ B 0` a morphism from a connected scheme
with a geometric point `z` and a comparison `s` of the fibre functors at `z ∘ k` and at `u`.
Then for every `j` there is a comparison `t` of the fibre functors of `B j` at the image of `z`
and at the `j`-th base point of the chain, for which the square

```
π₁(Z, z) → π₁(B 0, u) → π₁(B j, ·)
π₁(Z, z) → π₁(B j, z ∘ k ∘ ⋯)
```

commutes. -/
theorem exists_fiberFunctorIso_chainGroupMap_comp (d : ∀ j, B j ⟶ B (j + 1))
    (u : GeometricPoint (B 0)) {Z : Scheme.{u}} [ConnectedSpace Z] (k : Z ⟶ B 0)
    (z : GeometricPoint Z)
    (s : finiteEtaleFiberFunctor (z.map k) ≅ finiteEtaleFiberFunctor u) (j : ℕ) :
    ∀ (kj : Z ⟶ B j), kj = k ≫ chainIncl d j →
      ∃ t : finiteEtaleFiberFunctor (z.map kj) ≅
        finiteEtaleFiberFunctor (chainPoint d u j),
        ∀ σ : EtaleFundamentalGroup Z z,
          chainGroupMap d u j
              (etaleFundamentalGroupMulEquiv s (etaleFundamentalGroupMap k z σ))
            = etaleFundamentalGroupMulEquiv t (etaleFundamentalGroupMap kj z σ) := by
  induction j with
  | zero =>
    intro kj hkj
    have hkj' : kj = k := by rw [hkj]; exact Category.comp_id k
    subst hkj'
    exact ⟨s, fun σ ↦ rfl⟩
  | succ j ih =>
    intro kj hkj
    obtain ⟨tj, htj⟩ := ih (k ≫ chainIncl d j) rfl
    have hkj' : kj = (k ≫ chainIncl d j) ≫ d j := by
      rw [hkj]
      exact (Category.assoc k (chainIncl d j) (d j)).symm
    subst hkj'
    refine ⟨fiberFunctorMapCompIso (k ≫ chainIncl d j) (d j) z ≪≫
      fiberFunctorTransportIso (d j) tj, fun σ ↦ ?_⟩
    refine Eq.trans ?_ (etaleFundamentalGroupMulEquiv_trans _ _ _).symm
    refine Eq.trans ?_ (congrArg
      (fun γ ↦ etaleFundamentalGroupMulEquiv (fiberFunctorTransportIso (d j) tj) γ)
      (etaleFundamentalGroupMulEquiv_mapCompIso (k ≫ chainIncl d j) (d j) z σ).symm)
    exact (congrArg (fun γ ↦ etaleFundamentalGroupMap (d j) (chainPoint d u j) γ) (htj σ)).trans
      (etaleFundamentalGroupMulEquiv_transportIso (d j) tj
        (etaleFundamentalGroupMap (k ≫ chainIncl d j) z σ)).symm

/-- The kernel of the composite of the first `j` steps of a chain is the kernel of the map
induced by the inclusion of the bottom stage into the `j`-th stage. -/
theorem ker_chainGroupMap_eq_ker_etaleFundamentalGroupMap (d : ∀ j, B j ⟶ B (j + 1))
    (u : GeometricPoint (B 0)) (j : ℕ) :
    MonoidHom.ker (chainGroupMap d u j).toMonoidHom =
      MonoidHom.ker (etaleFundamentalGroupMap (chainIncl d j) u).toMonoidHom := by
  cases j with
  | zero =>
    have : IsIso (chainIncl d 0) := inferInstanceAs (IsIso (CategoryStruct.id (B 0)))
    rw [MonoidHom.ker_eq_bot _
      (injective_etaleFundamentalGroupMap_of_isIso (chainIncl d 0) u)]
    exact MonoidHom.ker_id
  | succ j => exact ker_chainGroupMap_eq_ker_etaleFundamentalGroupMap_succ d u j

/-! ### The chain of opens: steps, removed points, and punctured opens -/

section Chain

variable {X : Scheme.{u}} {n : ℕ}

/-- The `j`-th step `X ∖ {xᵢ : j ≤ i} ⟶ X ∖ {xᵢ : j + 1 ≤ i}` of the chain of opens obtained by
removing the points `xᵢ` one at a time. -/
def chainStep (x : Fin n → X) (hclosed : ∀ i, IsClosed ({x i} : Set X)) (j : ℕ) :
    (chainOpen x hclosed j).toScheme ⟶ (chainOpen x hclosed (j + 1)).toScheme :=
  X.homOfLE (chainOpen_le_succ x hclosed j)

/-- A step of the chain is an open immersion, being an inclusion of opens of `X`. -/
instance isOpenImmersion_chainStep (x : Fin n → X) (hclosed : ∀ i, IsClosed ({x i} : Set X))
    (j : ℕ) : IsOpenImmersion (chainStep x hclosed j) :=
  inferInstanceAs (IsOpenImmersion (X.homOfLE (chainOpen_le_succ x hclosed j)))

variable (x : Fin n → X) (hclosed : ∀ i, IsClosed ({x i} : Set X))

/-- A step of the chain, followed by the inclusion of its target, is the inclusion of its
source. -/
theorem chainStep_comp_ι (j : ℕ) :
    chainStep x hclosed j ≫ (chainOpen x hclosed (j + 1)).ι = (chainOpen x hclosed j).ι :=
  X.homOfLE_ι _

/-- The inclusion of the bottom stage of the chain into the `j`-th stage, followed by the
inclusion of the `j`-th stage into `X`, is the inclusion of the bottom stage into `X`. -/
theorem chainIncl_comp_ι (j : ℕ) :
    chainIncl (chainStep x hclosed) j ≫ (chainOpen x hclosed j).ι =
      (chainOpen x hclosed 0).ι := by
  induction j with
  | zero => exact Category.id_comp _
  | succ j ih =>
    show (chainIncl (chainStep x hclosed) j ≫ chainStep x hclosed j) ≫ _ = _
    rw [Category.assoc, chainStep_comp_ι]
    exact ih

/-- For pairwise distinct points, the point removed by the `i`-th step is still present at the
next stage. -/
theorem notMem_chainRemoved_succ (hinj : Function.Injective x) (i : Fin n) :
    x i ∉ chainRemoved x ((i : ℕ) + 1) := by
  rintro ⟨k, hk, hxk⟩
  obtain rfl : k = i := hinj hxk
  simp only [Set.mem_ofPred_eq] at hk
  omega

/-- **The point removed by the `i`-th step of the chain**, as a point of the stage
`X ∖ {xⱼ : i + 1 ≤ j}` from which it is removed. -/
def chainRemovedPoint (hinj : Function.Injective x) (i : Fin n) :
    (chainOpen x hclosed ((i : ℕ) + 1)).toScheme :=
  ⟨x i, notMem_chainRemoved_succ x hinj i⟩

/-- The removed point lies over `xᵢ`. -/
theorem coe_chainRemovedPoint (hinj : Function.Injective x) (i : Fin n) :
    (chainOpen x hclosed ((i : ℕ) + 1)).ι.base (chainRemovedPoint x hclosed hinj i) = x i := by
  simp [chainRemovedPoint, Scheme.Opens.ι_apply]

/-- The `i`-th step of the chain removes exactly the point `xᵢ`: the points of the stage
`X ∖ {xⱼ : i + 1 ≤ j}` lying over a point removed at stage `i` form the singleton of the removed
point. -/
theorem preimage_chainRemoved_eq_singleton (hinj : Function.Injective x) (i : Fin n) :
    (chainOpen x hclosed ((i : ℕ) + 1)).ι.base ⁻¹' chainRemoved x (i : ℕ) =
      {chainRemovedPoint x hclosed hinj i} := by
  refine Set.eq_singleton_iff_unique_mem.mpr ⟨?_, fun p hp ↦ ?_⟩
  · refine Set.mem_preimage.mpr ⟨i, ?_, (coe_chainRemovedPoint x hclosed hinj i).symm⟩
    simp only [Set.mem_ofPred_eq]
    exact le_rfl
  · obtain ⟨k, hk, hxk⟩ := Set.mem_preimage.mp hp
    simp only [Set.mem_ofPred_eq] at hk
    have hp2 : (chainOpen x hclosed ((i : ℕ) + 1)).ι.base p ∉
        chainRemoved x ((i : ℕ) + 1) := p.2
    have hki : (k : ℕ) = (i : ℕ) := by
      by_contra hne
      exact hp2 ⟨k, by simp only [Set.mem_ofPred_eq]; omega, hxk⟩
    obtain rfl : k = i := Fin.ext hki
    exact (chainOpen x hclosed ((k : ℕ) + 1)).ι.isOpenEmbedding.injective
      ((((coe_chainRemovedPoint x hclosed hinj k).trans hxk).symm))

/-- The removed point is not in the image of the step that removes it. -/
theorem notMem_range_chainStep (hinj : Function.Injective x) (i : Fin n) :
    chainRemovedPoint x hclosed hinj i ∉ Set.range (chainStep x hclosed (i : ℕ)).base := by
  rw [← Set.mem_compl_iff, chainStep, compl_range_chainOpen_homOfLE,
    preimage_chainRemoved_eq_singleton x hclosed hinj i]
  exact Set.mem_singleton _

/-- The point removed by a step of the chain is a closed point of the stage it is removed
from. -/
theorem isClosed_chainRemovedPoint (hinj : Function.Injective x) (i : Fin n) :
    IsClosed ({chainRemovedPoint x hclosed hinj i} :
      Set (chainOpen x hclosed ((i : ℕ) + 1)).toScheme) :=
  isClosed_singleton_of_notMem_range_chainOpen_homOfLE x hclosed (i : ℕ) _
    (notMem_range_chainStep x hclosed hinj i)

/-- **The image of a step of the chain is the complement of the removed point.** -/
theorem range_chainStep (hinj : Function.Injective x) (i : Fin n) :
    Set.range (chainStep x hclosed (i : ℕ)).base =
      Set.range (puncturedOpen (isClosed_chainRemovedPoint x hclosed hinj i)).ι.base := by
  rw [Scheme.Opens.range_ι]
  apply compl_injective
  rw [chainStep, compl_range_chainOpen_homOfLE,
    preimage_chainRemoved_eq_singleton x hclosed hinj i]
  simp [puncturedOpen]

/-- **A step of the chain, read as the complement of the removed point.** The isomorphism from the
`i`-th stage of the chain onto the complement of the removed point in the next stage, compatible
with the inclusions into that stage. -/
def chainStepIso (hinj : Function.Injective x) (i : Fin n) :
    (chainOpen x hclosed (i : ℕ)).toScheme ≅
      (puncturedOpen (isClosed_chainRemovedPoint x hclosed hinj i)).toScheme :=
  IsOpenImmersion.isoOfRangeEq (chainStep x hclosed (i : ℕ))
    (puncturedOpen (isClosed_chainRemovedPoint x hclosed hinj i)).ι
    (range_chainStep x hclosed hinj i)

/-- The comparison isomorphism carries the inclusion of the complement of the removed point back
to the step of the chain. -/
theorem chainStepIso_inv_comp (hinj : Function.Injective x) (i : Fin n) :
    (chainStepIso x hclosed hinj i).inv ≫ chainStep x hclosed (i : ℕ) =
      (puncturedOpen (isClosed_chainRemovedPoint x hclosed hinj i)).ι :=
  IsOpenImmersion.isoOfRangeEq_inv_fac (chainStep x hclosed (i : ℕ))
    (puncturedOpen (isClosed_chainRemovedPoint x hclosed hinj i)).ι
    (range_chainStep x hclosed hinj i)

/-- If `U` is retrocompact in `X`, the complement of the removed point is retrocompact in the
stage it is removed from. -/
theorem quasiCompact_puncturedOpen_chainRemovedPoint (hinj : Function.Injective x) (i : Fin n)
    [QuasiCompact (chainOpen x hclosed 0).ι] :
    QuasiCompact (puncturedOpen (isClosed_chainRemovedPoint x hclosed hinj i)).ι := by
  rw [← chainStepIso_inv_comp x hclosed hinj i]
  have : QuasiCompact (chainStep x hclosed (i : ℕ)) :=
    quasiCompact_chainOpen_homOfLE x hclosed (i : ℕ)
  infer_instance

/-- If `X` and `U` are connected, the complement of the removed point in the stage it is removed
from is connected. -/
theorem connectedSpace_puncturedOpen_chainRemovedPoint (hinj : Function.Injective x) (i : Fin n)
    [ConnectedSpace (chainOpen x hclosed 0).toScheme] [ConnectedSpace X] :
    ConnectedSpace (puncturedOpen (isClosed_chainRemovedPoint x hclosed hinj i)).toScheme := by
  have : ConnectedSpace (chainOpen x hclosed (i : ℕ)).toScheme :=
    connectedSpace_chainOpen x hclosed (i : ℕ)
  exact (chainStepIso x hclosed hinj i).hom.surjective.connectedSpace
    (chainStepIso x hclosed hinj i).hom.continuous

/-- **The factorisation through `U`.** A morphism into the stage `X ∖ {xⱼ : i + 1 ≤ j}` whose
image consists of points generalising the removed point `xᵢ`, and which misses `xᵢ` itself, lands
in `U = X ∖ {x₀, …, xₙ₋₁}`. -/
theorem range_comp_ι_subset_range_chainOpen_zero (hinj : Function.Injective x) (i : Fin n)
    {Z : Scheme.{u}} (q : Z ⟶ (chainOpen x hclosed ((i : ℕ) + 1)).toScheme)
    (hne : ∀ a : Z, q.base a ≠ chainRemovedPoint x hclosed hinj i)
    (hsp : ∀ a : Z, q.base a ⤳ chainRemovedPoint x hclosed hinj i) :
    Set.range (q ≫ (chainOpen x hclosed ((i : ℕ) + 1)).ι).base ⊆
      Set.range (chainOpen x hclosed 0).ι.base := by
  rw [Scheme.Opens.range_ι]
  rintro _ ⟨a, rfl⟩
  rw [coe_chainOpen_zero]
  rintro ⟨k, hk⟩
  have hsp' : (chainOpen x hclosed ((i : ℕ) + 1)).ι.base (q.base a) ⤳
      (chainOpen x hclosed ((i : ℕ) + 1)).ι.base (chainRemovedPoint x hclosed hinj i) :=
    (hsp a).map (chainOpen x hclosed ((i : ℕ) + 1)).ι.continuous
  have hqa : (chainOpen x hclosed ((i : ℕ) + 1)).ι.base (q.base a) = x k :=
    (Scheme.Hom.comp_apply q (chainOpen x hclosed ((i : ℕ) + 1)).ι a).symm.trans hk.symm
  rw [hqa, coe_chainRemovedPoint] at hsp'
  have hmem : x i ∈ closure ({x k} : Set X) := specializes_iff_mem_closure.mp hsp'
  rw [(hclosed k).closure_eq] at hmem
  have hik : i = k := hinj (Set.eq_of_mem_singleton hmem)
  subst hik
  exact hne a ((chainOpen x hclosed ((i : ℕ) + 1)).ι.isOpenEmbedding.injective
    (hqa.trans (coe_chainRemovedPoint x hclosed hinj i).symm))

end Chain

/-! ### The punctured strict henselization at the removed point -/

section Local

variable {X : Scheme.{u}} {n : ℕ} (x : Fin n → X) (hclosed : ∀ i, IsClosed ({x i} : Set X))
  (hinj : Function.Injective x) (i : Fin n)

/-- The local ring at the point `xᵢ` which the `i`-th step of the chain removes, taken in the
stage `X ∖ {xⱼ : i + 1 ≤ j}` the point is removed from. -/
abbrev chainStalk : CommRingCat.{u} :=
  (chainOpen x hclosed ((i : ℕ) + 1)).toScheme.presheaf.stalk
    (chainRemovedPoint x hclosed hinj i)

variable (Ash : Type u) [CommRing Ash] [Algebra ↥(chainStalk x hclosed hinj i) Ash]

/-- The morphism `Spec Aᵢˢʰ ⟶ X ∖ {xⱼ : i + 1 ≤ j}` attached to a strict henselization `Aᵢˢʰ` of
the local ring at the removed point. -/
def chainLocalHom : Spec (CommRingCat.of Ash) ⟶ (chainOpen x hclosed ((i : ℕ) + 1)).toScheme :=
  Spec.map (CommRingCat.ofHom (algebraMap ↥(chainStalk x hclosed hinj i) Ash)) ≫
    (chainOpen x hclosed ((i : ℕ) + 1)).toScheme.fromSpecStalk
      (chainRemovedPoint x hclosed hinj i)

/-- `Uᵢˢʰ`: the preimage in `Spec Aᵢˢʰ` of the complement of the removed point. -/
def chainLocalPunctured : (Spec (CommRingCat.of Ash)).Opens :=
  chainLocalHom x hclosed hinj i Ash ⁻¹ᵁ
    puncturedOpen (isClosed_chainRemovedPoint x hclosed hinj i)

/-- The morphism `Uᵢˢʰ ⟶ X ∖ {xᵢ} ∖ {xⱼ : i + 1 ≤ j}` onto the complement of the removed
point. -/
def chainLocalRes : (chainLocalPunctured x hclosed hinj i Ash).toScheme ⟶
    (puncturedOpen (isClosed_chainRemovedPoint x hclosed hinj i)).toScheme :=
  chainLocalHom x hclosed hinj i Ash ∣_
    puncturedOpen (isClosed_chainRemovedPoint x hclosed hinj i)

/-- The image of `Uᵢˢʰ` in `X` is contained in `U`. -/
theorem range_chainLocal_subset_range_chainOpen_zero :
    Set.range (((chainLocalPunctured x hclosed hinj i Ash).ι ≫
        chainLocalHom x hclosed hinj i Ash) ≫
      (chainOpen x hclosed ((i : ℕ) + 1)).ι).base ⊆
      Set.range (chainOpen x hclosed 0).ι.base := by
  refine range_comp_ι_subset_range_chainOpen_zero x hclosed hinj i _ (fun a ↦ ?_) (fun a ↦ ?_)
  · have h : (chainLocalHom x hclosed hinj i Ash).base
        ((chainLocalPunctured x hclosed hinj i Ash).ι.base a) ∈
        puncturedOpen (isClosed_chainRemovedPoint x hclosed hinj i) := a.2
    rw [Scheme.Hom.comp_apply]
    simpa [puncturedOpen] using h
  · have hm : ((chainLocalPunctured x hclosed hinj i Ash).ι ≫
        chainLocalHom x hclosed hinj i Ash).base a ∈
        Set.range ((chainOpen x hclosed ((i : ℕ) + 1)).toScheme.fromSpecStalk
          (chainRemovedPoint x hclosed hinj i)).base := by
      refine ⟨(Spec.map (CommRingCat.ofHom
        (algebraMap ↥(chainStalk x hclosed hinj i) Ash))).base
          ((chainLocalPunctured x hclosed hinj i Ash).ι.base a), ?_⟩
      rw [Scheme.Hom.comp_apply, chainLocalHom, Scheme.Hom.comp_apply]
    rwa [Scheme.range_fromSpecStalk] at hm

/-- The lift `Uᵢˢʰ ⟶ U` of the morphism `Uᵢˢʰ ⟶ X`. -/
def chainLocalLift : (chainLocalPunctured x hclosed hinj i Ash).toScheme ⟶
    (chainOpen x hclosed 0).toScheme :=
  IsOpenImmersion.lift (chainOpen x hclosed 0).ι
    (((chainLocalPunctured x hclosed hinj i Ash).ι ≫ chainLocalHom x hclosed hinj i Ash) ≫
      (chainOpen x hclosed ((i : ℕ) + 1)).ι)
    (range_chainLocal_subset_range_chainOpen_zero x hclosed hinj i Ash)

/-- The lift of `Uᵢˢʰ` to `U` is a lift of its morphism to `X`. -/
theorem chainLocalLift_comp_ι :
    chainLocalLift x hclosed hinj i Ash ≫ (chainOpen x hclosed 0).ι =
      ((chainLocalPunctured x hclosed hinj i Ash).ι ≫ chainLocalHom x hclosed hinj i Ash) ≫
        (chainOpen x hclosed ((i : ℕ) + 1)).ι :=
  IsOpenImmersion.lift_fac (chainOpen x hclosed 0).ι _
    (range_chainLocal_subset_range_chainOpen_zero x hclosed hinj i Ash)

/-- **The triangle `Uᵢˢʰ ⟶ U ⟶ X ∖ {xⱼ : i ≤ j}` commutes.** The morphism of `Uᵢˢʰ` to the
`i`-th stage of the chain, read through `AlgebraicGeometry.chainStepIso`, is the lift to `U`
followed by the inclusion of `U` in that stage. -/
theorem chainLocalRes_comp_chainStepIso_inv :
    chainLocalRes x hclosed hinj i Ash ≫ (chainStepIso x hclosed hinj i).inv =
      chainLocalLift x hclosed hinj i Ash ≫ chainIncl (chainStep x hclosed) (i : ℕ) := by
  rw [← cancel_mono (chainOpen x hclosed (i : ℕ)).ι, Category.assoc, Category.assoc,
    chainIncl_comp_ι, chainLocalLift_comp_ι,
    ← chainStep_comp_ι x hclosed (i : ℕ), ← Category.assoc (chainStepIso x hclosed hinj i).inv,
    chainStepIso_inv_comp, ← Category.assoc]
  exact congrArg (· ≫ (chainOpen x hclosed ((i : ℕ) + 1)).ι)
    (morphismRestrict_ι (chainLocalHom x hclosed hinj i Ash)
      (puncturedOpen (isClosed_chainRemovedPoint x hclosed hinj i)))

end Local

/-! ### The local exact sequence at a closed point, unconditionally -/

section OnePoint

variable {Y : Scheme.{u}} {y : Y}

/-- At a closed point `y` of `Y`, the preimage of `Y ∖ {y}` in `Spec 𝒪_{Y,y}` is the punctured
spectrum of `𝒪_{Y,y}`. -/
private theorem fromSpecStalk_preimage_puncturedOpen_eq (hy : IsClosed ({y} : Set Y)) :
    Y.fromSpecStalk y ⁻¹ᵁ puncturedOpen hy = puncturedSpectrum ↥(Y.presheaf.stalk y) := by
  refine preimage_fromSpecStalk_eq_puncturedSpectrum (puncturedOpen hy) y
    (by simp [puncturedOpen]) fun z hz ↦ ?_
  obtain rfl : z = y := by simpa [puncturedOpen] using hz
  exact hy

/-- The punctured spectrum of the local ring at a closed point whose complement is retrocompact
is itself retrocompact. -/
theorem quasiCompact_puncturedSpectrum_stalk_ι (hy : IsClosed ({y} : Set Y))
    (hqc : QuasiCompact (puncturedOpen hy).ι) :
    QuasiCompact (puncturedSpectrum ↥(Y.presheaf.stalk y)).ι := by
  have h := MorphismProperty.of_isPullback
    (isPullback_morphismRestrict (Y.fromSpecStalk y) (puncturedOpen hy)) hqc
  rwa [fromSpecStalk_preimage_puncturedOpen_eq hy] at h

/-- Let `y` be a closed point of `Y` whose complement is retrocompact and let `Aˢʰ` be a strict
henselization of `𝒪_{Y,y}` with connected punctured spectrum. A finite étale cover of the
punctured spectrum of `𝒪_{Y,y}` whose base change to the punctured spectrum of `Aˢʰ` is a finite
coproduct of copies of the base is the restriction of a finite étale cover of `Spec 𝒪_{Y,y}`. -/
theorem descent_of_quasiCompact_puncturedOpen (hy : IsClosed ({y} : Set Y))
    (hqc : QuasiCompact (puncturedOpen hy).ι)
    (κsep : Type u) [Field κsep]
    [Algebra (maximalIdeal ↥(Y.presheaf.stalk y)).ResidueField κsep]
    [IsSepClosure (maximalIdeal ↥(Y.presheaf.stalk y)).ResidueField κsep]
    (Ash : Type u) [CommRing Ash] [IsLocalRing Ash] [Algebra ↥(Y.presheaf.stalk y) Ash]
    (hAsh : Stacks.StrictHenselization.IsStrictHenselization ↥(Y.presheaf.stalk y) κsep Ash)
    (hconnected : _root_.IsConnected ({closedPoint Ash}ᶜ : Set (PrimeSpectrum Ash)))
    (w : GeometricPoint ((Spec.map (CommRingCat.ofHom
      (algebraMap ↥(Y.presheaf.stalk y) Ash)) ≫ Y.fromSpecStalk y) ⁻¹ᵁ
        puncturedOpen hy).toScheme) :
    ∀ V : FiniteEtaleOver (puncturedSpectrum ↥(Y.presheaf.stalk y)).toScheme,
      IsFiniteCoproductOfTerminal
          ((finiteEtaleBaseChange (Spec.map (CommRingCat.ofHom
            (algebraMap ↥(Y.presheaf.stalk y) Ash)) ∣_
              puncturedSpectrum ↥(Y.presheaf.stalk y))).obj V) →
        (finiteEtaleBaseChange (puncturedSpectrum ↥(Y.presheaf.stalk y)).ι).essImage V := by
  have : QuasiCompact (puncturedSpectrum ↥(Y.presheaf.stalk y)).ι :=
    quasiCompact_puncturedSpectrum_stalk_ι hy hqc
  have hopen : (Spec.map (CommRingCat.ofHom
      (algebraMap ↥(Y.presheaf.stalk y) Ash)) ≫ Y.fromSpecStalk y) ⁻¹ᵁ puncturedOpen hy =
      Spec.map (CommRingCat.ofHom (algebraMap ↥(Y.presheaf.stalk y) Ash)) ⁻¹ᵁ
        puncturedSpectrum ↥(Y.presheaf.stalk y) := by
    rw [Scheme.Hom.comp_preimage, fromSpecStalk_preimage_puncturedOpen_eq hy]
  exact essImage_finiteEtaleBaseChange_puncturedSpectrum _ κsep Ash hAsh hconnected (hopen ▸ w)

/-- **The local exact sequence at one closed point of a scheme, unconditionally.** Let `y` be a
closed point of a connected scheme `Y` whose complement `V = Y ∖ {y}` is connected and
retrocompact, let `Aˢʰ` be a strict henselization of `𝒪_{Y,y}`, let `Vˢʰ` be the preimage of `V`
in `Spec Aˢʰ` and let `ū` be a geometric point of `Vˢʰ`. If the punctured spectrum of every
strict henselization of `𝒪_{Y,y}` is connected, then

```
π₁(Vˢʰ, ū) → π₁(V, ū) → π₁(Y, ū) → 1
```

is exact. -/
theorem isExactSequence_etaleFundamentalGroupMap_puncturedOpen_of_quasiCompact
    (hy : IsClosed ({y} : Set Y)) (hqc : QuasiCompact (puncturedOpen hy).ι)
    [ConnectedSpace Y] [ConnectedSpace (puncturedOpen hy).toScheme]
    (hconn : IsConnectedPuncturedStrictHenselization ↥(Y.presheaf.stalk y))
    (κsep : Type u) [Field κsep]
    [Algebra (maximalIdeal ↥(Y.presheaf.stalk y)).ResidueField κsep]
    [IsSepClosure (maximalIdeal ↥(Y.presheaf.stalk y)).ResidueField κsep]
    (Ash : Type u) [CommRing Ash] [IsLocalRing Ash] [Algebra ↥(Y.presheaf.stalk y) Ash]
    (hAsh : Stacks.StrictHenselization.IsStrictHenselization ↥(Y.presheaf.stalk y) κsep Ash)
    (w : GeometricPoint ((Spec.map (CommRingCat.ofHom
      (algebraMap ↥(Y.presheaf.stalk y) Ash)) ≫ Y.fromSpecStalk y) ⁻¹ᵁ
        puncturedOpen hy).toScheme) :
    letI : ConnectedSpace ((Spec.map (CommRingCat.ofHom
        (algebraMap ↥(Y.presheaf.stalk y) Ash)) ≫ Y.fromSpecStalk y) ⁻¹ᵁ puncturedOpen hy) :=
      connectedSpace_preimage_puncturedOpen_of_isStrictHenselization hy κsep Ash hAsh
        (hconn κsep Ash hAsh)
    IsExactSequence
      (etaleFundamentalGroupMap ((Spec.map (CommRingCat.ofHom
        (algebraMap ↥(Y.presheaf.stalk y) Ash)) ≫ Y.fromSpecStalk y) ∣_ puncturedOpen hy) w)
      (etaleFundamentalGroupMap (puncturedOpen hy).ι
        (w.map ((Spec.map (CommRingCat.ofHom (algebraMap ↥(Y.presheaf.stalk y) Ash)) ≫
          Y.fromSpecStalk y) ∣_ puncturedOpen hy))) :=
  isExactSequence_etaleFundamentalGroupMap_puncturedOpen hy hqc hconn κsep Ash hAsh
    (descent_of_quasiCompact_puncturedOpen hy hqc κsep Ash hAsh (hconn κsep Ash hAsh) w) w

end OnePoint

/-! ### The kernel clause of Stacks 0BSC -/

section Main

variable {X : Scheme.{u}} {n : ℕ} (x : Fin n → X) (hclosed : ∀ i, IsClosed ({x i} : Set X))
  (hinj : Function.Injective x)

/-- After removing every point, the inclusion of the last stage of the chain is an isomorphism. -/
private theorem isIso_ι_chainOpen_length : IsIso (chainOpen x hclosed n).ι := by
  rw [chainOpen_eq_top x hclosed (le_refl n)]
  exact (Scheme.topIso X).isIso_hom

open Stacks.FundamentalGroup in
/-- **The kernel of `π₁(U) ⟶ π₁(X)`.** Let `X` be a connected scheme, let
`x₀, …, xₙ₋₁ ∈ X` be pairwise distinct closed points and let `U = X ∖ {x₀, …, xₙ₋₁}`, assumed
connected and retrocompact in `X`. Let `Aᵢˢʰ` be a strict henselization of the local ring at `xᵢ`
and let `Uᵢˢʰ` be the preimage of the complement of `xᵢ` in `Spec Aᵢˢʰ`, that is, the punctured
spectrum of `Aᵢˢʰ`; assume every punctured spectrum of every strict henselization of that local
ring is connected. Let `ū` be a geometric point of `U`, let `ūᵢ` be a geometric point of `Uᵢˢʰ`
and let `s i` compare the geometric fibre functors of `U` at the image of `ūᵢ` and at `ū`. Then

```
ker (π₁(U, ū) ⟶ π₁(X, ū))
```

is the smallest closed normal subgroup of `π₁(U, ū)` containing the images of the maps
`π₁(Uᵢˢʰ, ūᵢ) ⟶ π₁(U, ū)`, each read through `s i`. -/
@[stacks 0BSC "the kernel clause, in union-of-images form, with the factorisation `Uᵢˢʰ ⟶ U` \
proved; the removed points are assumed pairwise distinct, and hypothesis (2) is stated at the \
stalks of the stages of the chain, where it is used", sga "7 II 2.3.1" "partial"]
theorem ker_etaleFundamentalGroupMap_eq_closedNormalClosure_biUnion_range
    [ConnectedSpace X] [ConnectedSpace (chainOpen x hclosed 0).toScheme]
    [QuasiCompact (chainOpen x hclosed 0).ι]
    (hconn : ∀ (j : ℕ) (y : (chainOpen x hclosed (j + 1)).toScheme),
      y ∉ Set.range (chainStep x hclosed j).base →
        IsConnectedPuncturedStrictHenselization
          ↥((chainOpen x hclosed (j + 1)).toScheme.presheaf.stalk y))
    (κsep : Fin n → Type u) [∀ i, Field (κsep i)]
    [∀ i, Algebra (maximalIdeal ↥(chainStalk x hclosed hinj i)).ResidueField (κsep i)]
    [∀ i, IsSepClosure (maximalIdeal ↥(chainStalk x hclosed hinj i)).ResidueField (κsep i)]
    (Ash : Fin n → Type u) [∀ i, CommRing (Ash i)] [∀ i, IsLocalRing (Ash i)]
    [∀ i, Algebra ↥(chainStalk x hclosed hinj i) (Ash i)]
    (hAsh : ∀ i, Stacks.StrictHenselization.IsStrictHenselization
      ↥(chainStalk x hclosed hinj i) (κsep i) (Ash i))
    (u : GeometricPoint (chainOpen x hclosed 0).toScheme)
    (w : ∀ i, GeometricPoint (chainLocalPunctured x hclosed hinj i (Ash i)).toScheme)
    (s : ∀ i, finiteEtaleFiberFunctor ((w i).map (chainLocalLift x hclosed hinj i (Ash i))) ≅
      finiteEtaleFiberFunctor u) :
    letI : ∀ i : Fin n, ConnectedSpace (chainLocalPunctured x hclosed hinj i (Ash i)) :=
      fun i ↦ connectedSpace_preimage_puncturedOpen_of_isStrictHenselization
        (isClosed_chainRemovedPoint x hclosed hinj i) (κsep i) (Ash i) (hAsh i)
        (hconn (i : ℕ) (chainRemovedPoint x hclosed hinj i)
          (notMem_range_chainStep x hclosed hinj i) (κsep i) (Ash i) (hAsh i))
    MonoidHom.ker (etaleFundamentalGroupMap (chainOpen x hclosed 0).ι u).toMonoidHom =
      (Subgroup.normalClosure (⋃ i : Fin n, Set.range
        ((etaleFundamentalGroupChange (s i)).comp
          (etaleFundamentalGroupMap (chainLocalLift x hclosed hinj i (Ash i))
            (w i))))).topologicalClosure := by
  classical
  let hlc : ∀ i : Fin n, ConnectedSpace (chainLocalPunctured x hclosed hinj i (Ash i)) :=
    fun i ↦ connectedSpace_preimage_puncturedOpen_of_isStrictHenselization
      (isClosed_chainRemovedPoint x hclosed hinj i) (κsep i) (Ash i) (hAsh i)
      (hconn (i : ℕ) (chainRemovedPoint x hclosed hinj i)
        (notMem_range_chainStep x hclosed hinj i) (κsep i) (Ash i) (hAsh i))
  have hcs : ∀ j, ConnectedSpace (chainOpen x hclosed j).toScheme :=
    connectedSpace_chainOpen x hclosed
  have hsurj : ∀ j, Function.Surjective (etaleFundamentalGroupMap (chainStep x hclosed j)
      (chainPoint (chainStep x hclosed) u j)) := fun j ↦
    surjective_etaleFundamentalGroupMap_chainOpen_homOfLE x hclosed j (fun y hy ↦ hconn j y hy)
      (chainPoint (chainStep x hclosed) u j)
  have hkeri : ∀ (j : ℕ) (hj : j < n),
      MonoidHom.ker (etaleFundamentalGroupMap (chainStep x hclosed j)
          (chainPoint (chainStep x hclosed) u j)).toMonoidHom =
        (Subgroup.normalClosure (Set.range ((chainGroupMap (chainStep x hclosed) u j).comp
          ((etaleFundamentalGroupChange (s ⟨j, hj⟩)).comp
            (etaleFundamentalGroupMap
              (chainLocalLift x hclosed hinj ⟨j, hj⟩ (Ash ⟨j, hj⟩))
              (w ⟨j, hj⟩)))))).topologicalClosure := by
    intro j hj
    have hqcp : QuasiCompact
        (puncturedOpen (isClosed_chainRemovedPoint x hclosed hinj ⟨j, hj⟩)).ι :=
      quasiCompact_puncturedOpen_chainRemovedPoint x hclosed hinj ⟨j, hj⟩
    have hcp : ConnectedSpace
        (puncturedOpen (isClosed_chainRemovedPoint x hclosed hinj ⟨j, hj⟩)).toScheme :=
      connectedSpace_puncturedOpen_chainRemovedPoint x hclosed hinj ⟨j, hj⟩
    have h3 := (isExactSequence_etaleFundamentalGroupMap_puncturedOpen_of_quasiCompact
      (isClosed_chainRemovedPoint x hclosed hinj ⟨j, hj⟩) hqcp
      (hconn j (chainRemovedPoint x hclosed hinj ⟨j, hj⟩)
        (notMem_range_chainStep x hclosed hinj ⟨j, hj⟩)) (κsep ⟨j, hj⟩) (Ash ⟨j, hj⟩)
      (hAsh ⟨j, hj⟩) (w ⟨j, hj⟩)).2.2
    rw [← chainStepIso_inv_comp x hclosed hinj ⟨j, hj⟩] at h3
    obtain ⟨t', ht'⟩ := exists_fiberFunctorIso_chainGroupMap_comp (chainStep x hclosed) u
      (chainLocalLift x hclosed hinj ⟨j, hj⟩ (Ash ⟨j, hj⟩)) (w ⟨j, hj⟩) (s ⟨j, hj⟩) j
      (chainLocalRes x hclosed hinj ⟨j, hj⟩ (Ash ⟨j, hj⟩) ≫
        (chainStepIso x hclosed hinj ⟨j, hj⟩).inv)
      (chainLocalRes_comp_chainStepIso_inv x hclosed hinj ⟨j, hj⟩ (Ash ⟨j, hj⟩))
    refine Eq.trans (ker_etaleFundamentalGroupMap_of_iso
      (chainLocalRes x hclosed hinj ⟨j, hj⟩ (Ash ⟨j, hj⟩))
      (chainStepIso x hclosed hinj ⟨j, hj⟩) (chainStep x hclosed j) (w ⟨j, hj⟩)
      (chainPoint (chainStep x hclosed) u j)
      ((fiberFunctorMapCompIso (chainLocalRes x hclosed hinj ⟨j, hj⟩ (Ash ⟨j, hj⟩))
        (chainStepIso x hclosed hinj ⟨j, hj⟩).inv (w ⟨j, hj⟩)).symm ≪≫ t') h3) ?_
    refine congrArg (fun T ↦ (Subgroup.normalClosure T).topologicalClosure) ?_
    refine congrArg Set.range (funext fun σ ↦ ?_)
    have hcomp := etaleFundamentalGroupMulEquiv_mapCompIso
      (chainLocalRes x hclosed hinj ⟨j, hj⟩ (Ash ⟨j, hj⟩))
      (chainStepIso x hclosed hinj ⟨j, hj⟩).inv (w ⟨j, hj⟩) σ
    show etaleFundamentalGroupMulEquiv
        ((fiberFunctorMapCompIso (chainLocalRes x hclosed hinj ⟨j, hj⟩ (Ash ⟨j, hj⟩))
          (chainStepIso x hclosed hinj ⟨j, hj⟩).inv (w ⟨j, hj⟩)).symm ≪≫ t')
        (etaleFundamentalGroupMap (chainStepIso x hclosed hinj ⟨j, hj⟩).inv
          ((w ⟨j, hj⟩).map (chainLocalRes x hclosed hinj ⟨j, hj⟩ (Ash ⟨j, hj⟩)))
          (etaleFundamentalGroupMap (chainLocalRes x hclosed hinj ⟨j, hj⟩ (Ash ⟨j, hj⟩))
            (w ⟨j, hj⟩) σ)) =
      chainGroupMap (chainStep x hclosed) u j
        (etaleFundamentalGroupMulEquiv (s ⟨j, hj⟩)
          (etaleFundamentalGroupMap (chainLocalLift x hclosed hinj ⟨j, hj⟩ (Ash ⟨j, hj⟩))
            (w ⟨j, hj⟩) σ))
    rw [etaleFundamentalGroupMulEquiv_trans, ← hcomp,
      etaleFundamentalGroupMulEquiv_symm_apply_apply]
    exact (ht' σ).symm
  let G : ℕ → Subgroup (EtaleFundamentalGroup (chainOpen x hclosed 0).toScheme u) := fun j ↦
    if hj : j < n then
      MonoidHom.range ((etaleFundamentalGroupChange (s ⟨j, hj⟩)).comp
        (etaleFundamentalGroupMap (chainLocalLift x hclosed hinj ⟨j, hj⟩ (Ash ⟨j, hj⟩))
          (w ⟨j, hj⟩))).toMonoidHom
    else Subgroup.comap (chainGroupMap (chainStep x hclosed) u j).toMonoidHom
      (MonoidHom.ker (etaleFundamentalGroupMap (chainStep x hclosed j)
        (chainPoint (chainStep x hclosed) u j)).toMonoidHom)
  have hG : ∀ (j : ℕ) (hj : j < n), G j =
      MonoidHom.range ((etaleFundamentalGroupChange (s ⟨j, hj⟩)).comp
        (etaleFundamentalGroupMap (chainLocalLift x hclosed hinj ⟨j, hj⟩ (Ash ⟨j, hj⟩))
          (w ⟨j, hj⟩))).toMonoidHom := fun j hj ↦ dite_eq_left hj
  have hGrange : ∀ j, Set.range ((chainGroupMap (chainStep x hclosed) u j).comp
      (subtypeContinuousMonoidHom (G j))) =
      chainGroupMap (chainStep x hclosed) u j '' (G j : Set _) := by
    intro j
    rw [show (⇑((chainGroupMap (chainStep x hclosed) u j).comp
        (subtypeContinuousMonoidHom (G j)))) =
        (⇑(chainGroupMap (chainStep x hclosed) u j)) ∘ (⇑(subtypeContinuousMonoidHom (G j)))
      from rfl, Set.range_comp, range_subtypeContinuousMonoidHom]
  have hkerall : ∀ j, MonoidHom.ker (etaleFundamentalGroupMap (chainStep x hclosed j)
        (chainPoint (chainStep x hclosed) u j)).toMonoidHom =
      (Subgroup.normalClosure (Set.range ((chainGroupMap (chainStep x hclosed) u j).comp
        (subtypeContinuousMonoidHom (G j))))).topologicalClosure := by
    intro j
    by_cases hj : j < n
    · refine Eq.trans (hkeri j hj) ?_
      refine congrArg (fun T ↦ (Subgroup.normalClosure T).topologicalClosure) ?_
      rw [hGrange j, hG j hj, MonoidHom.coe_range, ← Set.range_comp]
      rfl
    · have hT2 := t2Space_etaleFundamentalGroup (chainOpen x hclosed (j + 1)).toScheme
        (chainPoint (chainStep x hclosed) u (j + 1))
      rw [hGrange j, show G j = Subgroup.comap
          (chainGroupMap (chainStep x hclosed) u j).toMonoidHom
          (MonoidHom.ker (etaleFundamentalGroupMap (chainStep x hclosed j)
            (chainPoint (chainStep x hclosed) u j)).toMonoidHom) from dite_eq_right hj,
        show (⇑(chainGroupMap (chainStep x hclosed) u j)) =
          (⇑(chainGroupMap (chainStep x hclosed) u j).toMonoidHom) from rfl,
        ← Subgroup.coe_map, Subgroup.map_comap_eq_self_of_surjective
          (surjective_chainGroupMap (chainStep x hclosed) u hsurj j)]
      exact (closedNormalClosure_coe_eq_self _ (isClosed_ker _)).symm
  have hchain := ker_chainGroupMap_eq_closedNormalClosure_biUnion_range (chainStep x hclosed) u
    (fun j ↦ subtypeContinuousMonoidHom (G j)) hsurj hkerall n
  have := isIso_ι_chainOpen_length x hclosed (n := n)
  have hfinal : MonoidHom.ker
      (etaleFundamentalGroupMap (chainOpen x hclosed 0).ι u).toMonoidHom =
      MonoidHom.ker (chainGroupMap (chainStep x hclosed) u n).toMonoidHom := by
    rw [ker_chainGroupMap_eq_ker_etaleFundamentalGroupMap, ← chainIncl_comp_ι x hclosed n]
    exact ker_etaleFundamentalGroupMap_comp_isIso (chainIncl (chainStep x hclosed) n)
      (chainOpen x hclosed n).ι u
  rw [hfinal, hchain]
  refine congrArg (fun T ↦ (Subgroup.normalClosure T).topologicalClosure) ?_
  ext γ
  simp only [Set.mem_iUnion, Finset.mem_range, range_subtypeContinuousMonoidHom]
  constructor
  · rintro ⟨j, hj, hγ⟩
    rw [hG j hj, MonoidHom.coe_range] at hγ
    exact ⟨⟨j, hj⟩, hγ⟩
  · rintro ⟨i, hγ⟩
    refine ⟨(i : ℕ), i.isLt, ?_⟩
    rw [hG i i.isLt, MonoidHom.coe_range]
    exact hγ

/-- The map induced by a composite on étale fundamental groups is surjective if the maps induced
by both factors are. -/
private theorem surjective_etaleFundamentalGroupMap_comp {A B C : Scheme.{u}} [ConnectedSpace A]
    [ConnectedSpace B] [ConnectedSpace C] (a : A ⟶ B) (b : B ⟶ C) (p : GeometricPoint A)
    (ha : Function.Surjective (etaleFundamentalGroupMap a p))
    (hb : Function.Surjective (etaleFundamentalGroupMap b (p.map a))) :
    Function.Surjective (etaleFundamentalGroupMap (a ≫ b) p) := by
  intro ρ
  obtain ⟨τ, hτ⟩ := hb (etaleFundamentalGroupMulEquiv (fiberFunctorMapCompIso a b p) ρ)
  obtain ⟨σ, hσ⟩ := ha τ
  refine ⟨σ, (etaleFundamentalGroupMulEquiv (fiberFunctorMapCompIso a b p)).injective ?_⟩
  rw [etaleFundamentalGroupMulEquiv_mapCompIso, hσ, hτ]

open Stacks.FundamentalGroup in
/-- Let `X` be a connected scheme, let
`x₀, …, xₙ₋₁ ∈ X` be pairwise distinct closed points and let `U = X ∖ {x₀, …, xₙ₋₁}`, which is
`AlgebraicGeometry.chainOpen x hclosed 0`. Assume

1. `U` is connected and retrocompact in `X` — `[ConnectedSpace (chainOpen x hclosed 0).toScheme]`
   and `[QuasiCompact (chainOpen x hclosed 0).ι]`;
2. for each `i` the punctured spectrum `Uᵢˢʰ` of the strict henselization of the local ring at
   `xᵢ` is connected — `hconn`.

Then for every geometric point `ū` of `U` the map `π₁(U, ū) ⟶ π₁(X, ū)` is surjective, and its
kernel is the smallest closed normal subgroup of `π₁(U, ū)` containing the images of the maps
`π₁(Uᵢˢʰ, ūᵢ) ⟶ π₁(U, ū)` for `i = 0, …, n - 1`. -/
@[stacks 0BSC "both clauses, surjectivity and the kernel, under one set of hypotheses; the \
removed points are assumed pairwise distinct, and hypothesis (2) is stated at the stalks of the \
stages of the chain, where it is used"]
theorem surjective_and_ker_etaleFundamentalGroupMap_of_finite_isClosed_compl
    [ConnectedSpace X] [ConnectedSpace (chainOpen x hclosed 0).toScheme]
    [QuasiCompact (chainOpen x hclosed 0).ι]
    (hconn : ∀ (j : ℕ) (y : (chainOpen x hclosed (j + 1)).toScheme),
      y ∉ Set.range (chainStep x hclosed j).base →
        IsConnectedPuncturedStrictHenselization
          ↥((chainOpen x hclosed (j + 1)).toScheme.presheaf.stalk y))
    (κsep : Fin n → Type u) [∀ i, Field (κsep i)]
    [∀ i, Algebra (maximalIdeal ↥(chainStalk x hclosed hinj i)).ResidueField (κsep i)]
    [∀ i, IsSepClosure (maximalIdeal ↥(chainStalk x hclosed hinj i)).ResidueField (κsep i)]
    (Ash : Fin n → Type u) [∀ i, CommRing (Ash i)] [∀ i, IsLocalRing (Ash i)]
    [∀ i, Algebra ↥(chainStalk x hclosed hinj i) (Ash i)]
    (hAsh : ∀ i, Stacks.StrictHenselization.IsStrictHenselization
      ↥(chainStalk x hclosed hinj i) (κsep i) (Ash i))
    (u : GeometricPoint (chainOpen x hclosed 0).toScheme)
    (w : ∀ i, GeometricPoint (chainLocalPunctured x hclosed hinj i (Ash i)).toScheme)
    (s : ∀ i, finiteEtaleFiberFunctor ((w i).map (chainLocalLift x hclosed hinj i (Ash i))) ≅
      finiteEtaleFiberFunctor u) :
    letI : ∀ i : Fin n, ConnectedSpace (chainLocalPunctured x hclosed hinj i (Ash i)) :=
      fun i ↦ connectedSpace_preimage_puncturedOpen_of_isStrictHenselization
        (isClosed_chainRemovedPoint x hclosed hinj i) (κsep i) (Ash i) (hAsh i)
        (hconn (i : ℕ) (chainRemovedPoint x hclosed hinj i)
          (notMem_range_chainStep x hclosed hinj i) (κsep i) (Ash i) (hAsh i))
    Function.Surjective (etaleFundamentalGroupMap (chainOpen x hclosed 0).ι u) ∧
      MonoidHom.ker (etaleFundamentalGroupMap (chainOpen x hclosed 0).ι u).toMonoidHom =
        (Subgroup.normalClosure (⋃ i : Fin n, Set.range
          ((etaleFundamentalGroupChange (s i)).comp
            (etaleFundamentalGroupMap (chainLocalLift x hclosed hinj i (Ash i))
              (w i))))).topologicalClosure := by
  have hcs : ∀ j, ConnectedSpace (chainOpen x hclosed j).toScheme :=
    connectedSpace_chainOpen x hclosed
  have hstep : ∀ (j : ℕ) (v : GeometricPoint (chainOpen x hclosed j).toScheme),
      Function.Surjective (etaleFundamentalGroupMap (chainStep x hclosed j) v) := fun j v ↦
    surjective_etaleFundamentalGroupMap_chainOpen_homOfLE x hclosed j (fun y hy ↦ hconn j y hy) v
  have hincl : ∀ j, Function.Surjective
      (etaleFundamentalGroupMap (chainIncl (chainStep x hclosed) j) u) := by
    intro j
    induction j with
    | zero =>
      have : IsIso (chainIncl (chainStep x hclosed) 0) :=
        inferInstanceAs (IsIso (CategoryStruct.id (chainOpen x hclosed 0).toScheme))
      exact surjective_etaleFundamentalGroupMap_of_isIso _ u
    | succ j ih =>
      exact surjective_etaleFundamentalGroupMap_comp _ (chainStep x hclosed j) u ih (hstep j _)
  have := isIso_ι_chainOpen_length x hclosed (n := n)
  refine ⟨?_, ker_etaleFundamentalGroupMap_eq_closedNormalClosure_biUnion_range x hclosed hinj
    hconn κsep Ash hAsh u w s⟩
  rw [← chainIncl_comp_ι x hclosed n]
  exact surjective_etaleFundamentalGroupMap_comp _ (chainOpen x hclosed n).ι u (hincl n)
    (surjective_etaleFundamentalGroupMap_of_isIso _ _)

end Main

end AlgebraicGeometry

end
