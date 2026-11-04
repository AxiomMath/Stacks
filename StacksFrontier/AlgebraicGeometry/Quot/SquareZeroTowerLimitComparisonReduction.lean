module

public import StacksFrontier.AlgebraicGeometry.Quot.SquareZeroTowerLimitComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.BaseRingTensorModuleSections

/-!
# Reducing the limit comparison of the tower problem to the sections `1 ⊗ m`

In the situation of `AlgebraicGeometry.ProperFlatFibre.towerProblem`, the body of the proof of
[Stacks Project, Tag 0D3X] identifies the map `φ : f^*𝒞_{Y₀/Y} ⟶ lim 𝒪_{X₀} ⊗ Iₙ` with the
canonical map `𝒪_{X₀} ⊗ lim Iₙ ⟶ lim 𝒪_{X₀} ⊗ Iₙ` (Stacks 0D3F). This file reduces that
identification to the values of `φ` on the sections `1 ⊗ m`, `m ∈ lim Iₙ`: if, for every `n`,
`1 ⊗ m` is carried by `φ` and the `n`-th projection to the section `1 ⊗ mₙ` read through
`AlgebraicGeometry.ProperFlatFibre.towerIdealSystemObjIso`, then the components
`towerIdealSystemObjIso` form a natural isomorphism and `φ` is the canonical map up to it.

## Main results

* `CategoryTheory.Limits.Types.exists_mem_sections_of_surjective_map`,
  `ModuleCat.surjective_limit_π_of_surjective_map`: in an inverse system indexed by `ℕ` with
  surjective transition maps, every projection out of the limit is surjective.
* `CategoryTheory.Limits.exists_iso_eq_limitPost_comp_of_sections`: the abstract reduction.
* `AlgebraicGeometry.ProperFlatFibre.exists_towerLimitKernelMap_eq_of_sections`: the
  identification of `φ` from its values on the sections `1 ⊗ m`.

## References

* [Stacks Project, Tag 0D3X](https://stacks.math.columbia.edu/tag/0D3X)
* [Stacks Project, Tag 0D3F](https://stacks.math.columbia.edu/tag/0D3F)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w

namespace CategoryTheory.Limits.Types

/-- **An element at level `n` of an inverse system of sets with surjective transitions extends to
a compatible family**: lifts are chosen at the levels above `n` and pushed down to all levels. -/
theorem exists_mem_sections_of_surjective_map {F : ℕᵒᵖ ⥤ Type v}
    (hF : ∀ n : ℕ, Function.Surjective (F.map (homOfLE (Nat.le_succ n)).op)) (n : ℕ)
    (x : F.obj (op n)) : ∃ s ∈ F.sections, s (op n) = x := by
  classical
  let b : (k : ℕ) → F.obj (op (n + k)) := Nat.rec x fun k y ↦ (hF (n + k) y).choose
  have hb : ∀ k : ℕ, F.map (homOfLE (Nat.le_succ (n + k))).op (b (k + 1)) = b k :=
    fun k ↦ (hF (n + k) (b k)).choose_spec
  have hchain : ∀ k l : ℕ, ∀ h : k ≤ l,
      F.map (homOfLE (Nat.add_le_add_left h n)).op (b l) = b k := by
    intro k l h
    induction l, h using Nat.le_induction with
    | base => exact FunctorToTypes.map_id_apply F (b k)
    | succ l hl ih => rw [← ih, ← hb l, ← FunctorToTypes.map_comp_apply]; rfl
  let s : (j : ℕᵒᵖ) → F.obj j := fun j ↦
    F.map (homOfLE (Nat.le_add_left (unop j) n)).op (b (unop j))
  refine ⟨s, fun {j j'} g ↦ ?_, ?_⟩
  · have hle : unop j' ≤ unop j := leOfHom g.unop
    show F.map g (F.map (homOfLE (Nat.le_add_left (unop j) n)).op (b (unop j))) =
      F.map (homOfLE (Nat.le_add_left (unop j') n)).op (b (unop j'))
    rw [← FunctorToTypes.map_comp_apply, ← hchain _ _ hle, ← FunctorToTypes.map_comp_apply]
    rfl
  · show F.map (homOfLE (Nat.le_add_left n n)).op (b n) = b 0
    rw [← hchain 0 n (Nat.zero_le n)]

end CategoryTheory.Limits.Types

namespace ModuleCat

/-- **The projections out of the limit of an inverse system of modules with surjective
transitions are surjective.** -/
theorem surjective_limit_π_of_surjective_map {R : Type u} [Ring R] (F : ℕᵒᵖ ⥤ ModuleCat.{u} R)
    (hF : ∀ n : ℕ, Function.Surjective (F.map (homOfLE (Nat.le_succ n)).op)) (n : ℕ) :
    Function.Surjective (limit.π F (op n)) := by
  intro x
  obtain ⟨s, hs, hsx⟩ := Types.exists_mem_sections_of_surjective_map (F := F ⋙ forget _)
    hF n x
  have hc := isLimitOfPreserves (forget (ModuleCat.{u} R)) (limit.isLimit F)
  refine ⟨(Types.isLimitEquivSections hc).symm ⟨s, hs⟩, ?_⟩
  exact (Types.isLimitEquivSections_symm_apply hc ⟨s, hs⟩ (op n)).trans hsx

end ModuleCat

namespace CategoryTheory.Limits

/-- **A map out of `T(lim Mₙ)` which is the canonical map on the sections `1 ⊗ m`.** Let
`T : R-Mod ⥤ 𝒞` carry sections `sec m : E ⟶ T(M)` natural in `M` which determine the maps out of
every `T(M)`, let `(Mₙ)` be an inverse system with surjective transitions and `(Nₙ)` an inverse
system in `𝒞` with isomorphisms `eₙ : T(Mₙ) ≅ Nₙ`. If `ψ : T(lim Mₙ) ⟶ lim Nₙ` followed by the
`n`-th projection carries `sec m` to `sec mₙ` read through `eₙ`, then the `eₙ` are natural and
`ψ` is the canonical map `T(lim Mₙ) ⟶ lim T(Mₙ)` followed by the limit of the `eₙ`. -/
theorem exists_iso_eq_limitPost_comp_of_sections {R : Type u} [Ring R] {𝒞 : Type w}
    [Category.{v} 𝒞] (T : ModuleCat.{u} R ⥤ 𝒞) {E : 𝒞}
    (sec : ∀ M : ModuleCat.{u} R, M → (E ⟶ T.obj M))
    (hsec : ∀ {M N : ModuleCat.{u} R} (g : M ⟶ N) (m : M), sec M m ≫ T.map g = sec N (g m))
    (hext : ∀ {M : ModuleCat.{u} R} {Q : 𝒞} {a b : T.obj M ⟶ Q},
      (∀ m : M, sec M m ≫ a = sec M m ≫ b) → a = b)
    (Msys : ℕᵒᵖ ⥤ ModuleCat.{u} R)
    (hMsurj : ∀ n : ℕ, Function.Surjective (Msys.map (homOfLE (Nat.le_succ n)).op))
    [HasLimit (Msys ⋙ T)] (N : ℕᵒᵖ ⥤ 𝒞) {hN : HasLimit N}
    (e : ∀ n : ℕ, T.obj (Msys.obj (op n)) ≅ N.obj (op n)) (ψ : T.obj (limit Msys) ⟶ limit N)
    (H : ∀ (n : ℕ) (m : ↑(limit Msys)), sec _ m ≫ ψ ≫ limit.π N (op n) =
      sec _ (limit.π Msys (op n) m) ≫ (e n).hom) :
    ∃ β : limit (Msys ⋙ T) ≅ limit N, ψ = limit.post Msys T ≫ β.hom := by
  have hnat : ∀ n : ℕ, (e (n + 1)).hom ≫ N.map (homOfLE (Nat.le_succ n)).op =
      T.map (Msys.map (homOfLE (Nat.le_succ n)).op) ≫ (e n).hom := by
    intro n
    refine hext fun m' => ?_
    obtain ⟨m, rfl⟩ := ModuleCat.surjective_limit_π_of_surjective_map Msys hMsurj (n + 1) m'
    rw [← reassoc_of% (H (n + 1) m), limit.w, reassoc_of% (hsec _ _), H n m,
      ← ConcreteCategory.comp_apply, limit.w]
  let τ : Msys ⋙ T ⟶ N := NatTrans.ofOpSequence (fun n => (e n).hom) fun n => (hnat n).symm
  have : ∀ j, IsIso (τ.app j) := fun j => by
    obtain ⟨n⟩ := j
    exact (inferInstance : IsIso (e n).hom)
  have : IsIso τ := NatIso.isIso_of_isIso_app _
  refine ⟨HasLimit.isoOfNatIso (asIso τ), limit.hom_ext fun j => ?_⟩
  obtain ⟨n⟩ := j
  rw [Category.assoc, HasLimit.isoOfNatIso_hom_π, asIso_hom, limit.post_π_assoc]
  refine hext fun m => ?_
  rw [H n m, reassoc_of% (hsec _ _)]
  rfl

end CategoryTheory.Limits

/- The global instance `Abelian (SheafOfModules.{max u v r w} O)` leaves a stuck universe
constraint against the `𝒪_X`-modules at the universe of the schemes. -/
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

namespace AlgebraicGeometry.ProperFlatFibre

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (ξ : ℕ ⥤ CartesianProperFlatSpaces B S hS)
  {Λ : Type u} [CommRing Λ] {R : ℕᵒᵖ ⥤ CommAlgCat.{u} Λ}
  (hsurj : ∀ {i j : ℕᵒᵖ} (f : i ⟶ j), Function.Surjective (R.map f).hom)
  (hsq : ∀ {i j : ℕᵒᵖ} (f : i ⟶ j), RingHom.ker (R.map f).hom.toRingHom ^ 2 = ⊥)
  (e : ∀ n : ℕ, (BigFppfOver.toScheme B S hS).obj (towerBase ξ n) ≅
    Spec (.of (R.obj (.op n))))
  (he : ∀ {i j : ℕ} (f : i ⟶ j),
    (BigFppfOver.toScheme B S hS).map ((ξ ⋙ cartesianProperFlatProjection B S hS).map f) ≫
      (e j).hom = (e i).hom ≫ Scheme.Spec.map (CommRingCat.ofHom (R.map f.op).hom.toRingHom).op)
  (cR : Cone R) (hcR : IsLimit cR) (c : Cocone (ξ ⋙ cartesianProperFlatProjection B S hS))
  (eLimit : (BigFppfOver.toScheme B S hS).obj c.pt ≅ Spec (.of cR.pt))
  (hc : ∀ n : ℕ, (BigFppfOver.toScheme B S hS).map (c.ι.app n) ≫ eLimit.hom =
    (e n).hom ≫ Scheme.Spec.map (CommRingCat.ofHom (cR.π.app (.op n)).hom.toRingHom).op)

/-- **`φ` is the canonical map `𝒪_{X₀} ⊗ lim Iₙ ⟶ lim 𝒪_{X₀} ⊗ Iₙ` once it is so on the sections
`1 ⊗ m`.** If, for every `n` and `m ∈ lim Iₙ`, the section `1 ⊗ m` of `𝒪_{X₀} ⊗ lim Iₙ`, read in
`f^*𝒞_{Y₀/Y}` (`AlgebraicGeometry.ProperFlatFibre.towerProblemKernelIso`), is carried by
`φ = towerLimitKernelMap` and the `n`-th projection to the section `1 ⊗ mₙ` read in
`𝒪_{X₀} ⊗ Iₙ` (`AlgebraicGeometry.ProperFlatFibre.towerIdealSystemObjIso`), then
`φ = α ≫ (𝒪 ⊗ lim Iₙ ⟶ lim 𝒪 ⊗ Iₙ) ≫ β` for an isomorphism `β`. -/
theorem exists_towerLimitKernelMap_eq_of_sections
    [HasLimit (towerBaseKernelSystem ξ hsurj hsq e ⋙ Space.baseRingTensorModule B S hS
      (towerSpace ξ 0) (Space.baseRingHomOfMap (towerStructureMap ξ 0)))]
    (H : ∀ (n : ℕ) (m : ↑(limit (towerBaseKernelSystem ξ hsurj hsq e))),
      Space.baseRingTensorSection B S hS (towerSpace ξ 0)
          (Space.baseRingHomOfMap (towerStructureMap ξ 0)) _ m ≫
        (towerProblemKernelIso ξ hsurj hsq e cR hcR c eLimit hc).inv ≫
        towerLimitKernelMap ξ hsurj hsq e he cR hcR c eLimit hc ≫
        limit.π (towerIdealSystem ξ hsurj hsq e he) (op n) =
      Space.baseRingTensorSection B S hS (towerSpace ξ 0)
          (Space.baseRingHomOfMap (towerStructureMap ξ 0)) _
          (limit.π (towerBaseKernelSystem ξ hsurj hsq e) (op n) m) ≫
        (towerIdealSystemObjIso ξ hsurj hsq e he n).hom) :
    ∃ β : limit (towerBaseKernelSystem ξ hsurj hsq e ⋙ Space.baseRingTensorModule B S hS
        (towerSpace ξ 0) (Space.baseRingHomOfMap (towerStructureMap ξ 0))) ≅
        ((towerProblem ξ hsurj hsq e cR hcR c eLimit hc).changeKernel
          (towerLimitKernelMap ξ hsurj hsq e he cR hcR c eLimit hc)).G,
      towerLimitKernelMap ξ hsurj hsq e he cR hcR c eLimit hc =
        (towerProblemKernelIso ξ hsurj hsq e cR hcR c eLimit hc).hom ≫
          limit.post (towerBaseKernelSystem ξ hsurj hsq e) (Space.baseRingTensorModule B S hS
            (towerSpace ξ 0) (Space.baseRingHomOfMap (towerStructureMap ξ 0))) ≫ β.hom := by
  obtain ⟨β, hβ⟩ := exists_iso_eq_limitPost_comp_of_sections
    (Space.baseRingTensorModule B S hS (towerSpace ξ 0)
      (Space.baseRingHomOfMap (towerStructureMap ξ 0)))
    (Space.baseRingTensorSection B S hS (towerSpace ξ 0)
      (Space.baseRingHomOfMap (towerStructureMap ξ 0)))
    (fun g m => Space.baseRingTensorSection_map B S hS (towerSpace ξ 0)
      (Space.baseRingHomOfMap (towerStructureMap ξ 0)) g m)
    (fun h => Space.baseRingTensorModule_hom_ext B S hS (towerSpace ξ 0)
      (Space.baseRingHomOfMap (towerStructureMap ξ 0)) h)
    (towerBaseKernelSystem ξ hsurj hsq e) (surjective_towerBaseKernelSystem_map ξ hsurj hsq e)
    (towerIdealSystem ξ hsurj hsq e he) (towerIdealSystemObjIso ξ hsurj hsq e he)
    ((towerProblemKernelIso ξ hsurj hsq e cR hcR c eLimit hc).inv ≫
      towerLimitKernelMap ξ hsurj hsq e he cR hcR c eLimit hc)
    (fun n m => (congrArg (_ ≫ ·) (Category.assoc _ _ _)).trans (H n m))
  exact ⟨β, (Iso.inv_comp_eq _).1 hβ⟩

end AlgebraicGeometry.ProperFlatFibre
