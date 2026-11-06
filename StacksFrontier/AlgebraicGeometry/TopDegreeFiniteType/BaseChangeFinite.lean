module

public import StacksFrontier.AlgebraicGeometry.AffineBaseChange.StructureSheaf
public import StacksFrontier.AlgebraicGeometry.AffineBaseChangeIso.Reduction
public import StacksFrontier.AlgebraicGeometry.AffineCohomologyComparison.Natural
public import StacksFrontier.AlgebraicGeometry.AffineQcohPushforward.Basic
public import StacksFrontier.AlgebraicGeometry.DerivedAffineMorphism.PullbackPushforwardTensor
public import StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.CoherentModuleFunctors.EquivalenceOverBase
public import StacksFrontier.AlgebraicGeometry.ProperCoherenceWitness.ChowStalk
public import StacksFrontier.AlgebraicGeometry.ProperCohomologyFinite.RingBase
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.SideCondition
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.AffineTilde
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.EilenbergWattsUnitor
public import StacksFrontier.AlgebraicGeometry.TopDegreeFiniteType.RingBaseCriterion
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.SituationInhabitant

/-!
# The base-change step of the proof of Tag 0EX4

The proof of [Stacks, Tag 0EX4] ends, once its limit arguments have reduced everything to a
Noetherian situation, with the following step. Let `g : X₀ ⟶ Y₀` be proper onto an affine
locally Noetherian base, let `d` be a degree above which the higher direct image along `g` of
every quasi-coherent module vanishes ([Stacks, Tag 02V7]), and let `F₀` be a coherent
`𝒪_{X₀}`-module. Let `u : Y ⟶ Y₀` be an arbitrary morphism from an affine scheme, let the square

`X --h--> X₀`, `X --f--> Y`, `X₀ --g--> Y₀`, `Y --u--> Y₀`

be cartesian, and let `F ≅ h^* F₀` on `X`. Then `H ᵈ (X, F)` is a finite `Γ(Y, ⊤)`-module. This
is the sentence *"and so `H ᵈ (X, F) = H ᵈ (X₀, F₀) ⊗_{R₀} R` is a finite `R`-module"* of the
source's last paragraph, and `moduleFinite_cohomology_of_isPullback` is it.

The route is the source's own.

* `u` is a morphism of affine schemes, hence affine, so `h` is affine by base change, and
  [Stacks, Tag 089W] identifies `H ᵈ (X, F)` with `H ᵈ (X₀, h_* F)` over `Γ(X₀, ⊤)`.
* `h_* 𝒪_X` is the pullback to `X₀` of the quasi-coherent module on `Spec Γ(Y₀, ⊤)` attached to
  `Γ(Y, ⊤)`: this is affine base change ([Stacks, Tag 02KG]) for the structure sheaf followed by
  [Stacks, Tag 01I9]. That is `pushforwardUnitIsoPullbackTilde`.
* The projection formula ([Stacks, Tag 0FZE]) and the symmetry of the tensor product then turn
  `h_* F ≅ h_*(h^* F₀)` into `F₀ ⊗_{𝒪_{X₀}} (g ≫ isoSpec)^* (Γ(Y, ⊤))~`, which is the value at
  `Γ(Y, ⊤)` of the geometric factor of the Eilenberg-Watts functor of [Stacks, Tag 0EX3] (b).
  That is `pushforwardIsoTensorTilde`.
* The affine case of [Stacks, Tag 0EX3] (b) — `topDegreeTensorCohomologyIso` of the directory
  `TopDegreeBaseChange` — evaluates that functor as `H ᵈ (X₀, F₀) ⊗_{Γ(Y₀, ⊤)} Γ(Y, ⊤)`, and
  [Stacks, Tag 02O6] makes `H ᵈ (X₀, F₀)` a finite `Γ(Y₀, ⊤)`-module.
* Each comparison above is shown to carry multiplication by a function pulled back from `Y`,
  which is what makes the composite `Γ(Y, ⊤)`-equivariant rather than merely
  `Γ(Y₀, ⊤)`-linear; those are the `…_smul` results. Only equivariance is needed, not
  injectivity: `moduleFinite_of_tmul_span` concludes from a surjection whose source is a base
  change of a finite module.

## Main results

All in the namespace `Stacks.AlgebraicGeometry.TopDegreeFiniteType`.

* `moduleFinite_cohomology_of_isPullback`: **the step above.**
* `situation`: the top-degree base-change situation of [Stacks, Tag 0EX3] carried by `g` and `d`
  at the identity square, and `moduleFinite_topDegreeCohomology`: [Stacks, Tag 02O6] read in it.
* `pushforwardUnitIsoPullbackTilde` and `pushforwardIsoTensorTilde`: the two sheaf comparisons,
  with `pushforwardUnitIsoPullbackTilde_smul` and `pushforwardIsoTensorTilde_smul`.
* `cohomologyIsoPushforward_smul_appTop`: [Stacks, Tag 089W] carries multiplication by a
  function pulled back from `Y`.
* `tensorSheaf_map_smul_left`: multiplying the left factor of a tensor product of module
  sheaves by a base scalar is multiplication by that scalar. The second-variable statement is
  `AlgebraicGeometry.tensorLeft_linear`; this is its first-variable companion, obtained from
  `AlgebraicGeometry.CoherentModuleFunctors.tensorRight_linear`.
* `moduleFinite_of_tmul_span`: the ring-theoretic endgame.

## What is and is not covered

Covered: the step above, for a proper `g` onto an affine locally Noetherian base, with the
vanishing of the higher direct images above `d` carried as the hypothesis `hvan` — that is
[Stacks, Tag 02V7] at `g`, proved elsewhere in this development.

Not covered: the rest of [Stacks, Tag 0EX4] — the localisation of the conclusion on the base,
the presentation of `Y` and of `X` as cofiltered limits of Noetherian data, and the descent of
the morphism, of the fibre-dimension bound and of the module to a finite stage. Nothing here
asserts [Stacks, Tag 0EX4] or [Stacks, Tag 0EX3], and **no `@[stacks]` attribute is attached to
anything in this file**; assembling this step into the tag is another file's business.

## References

* [Stacks Project, Tag 0EX4](https://stacks.math.columbia.edu/tag/0EX4)
* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
* [Stacks Project, Tag 02O6](https://stacks.math.columbia.edu/tag/02O6)
* [Stacks Project, Tag 02V7](https://stacks.math.columbia.edu/tag/02V7)
* [Stacks Project, Tag 089W](https://stacks.math.columbia.edu/tag/089W)
* [Stacks Project, Tag 0FZE](https://stacks.math.columbia.edu/tag/0FZE)
* [Stacks Project, Tag 02KG](https://stacks.math.columbia.edu/tag/02KG)
* [Stacks Project, Tag 01I9](https://stacks.math.columbia.edu/tag/01I9)
-/

@[expose] public section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.AffineBase

namespace Stacks.AlgebraicGeometry.TopDegreeFiniteType

noncomputable section

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] AlgebraicGeometry.modulesLinear baseSectionsAlgebra

/-! ### Finiteness after a base change of rings -/

open scoped TensorProduct in
/-- **Finiteness after a base change of rings, from a surjection on pure tensors.** Let `H` be a
finite `R₀`-module, let `M` be an `R₀`-module carrying a distinguished element `m₁` and an
`R`-action `act` for which every element of `M` is `act c m₁` for some `c`, and let
`ψ : H ⊗_{R₀} M → N` be an additive surjection onto an `R`-module `N` which is `R`-equivariant
in the right tensor factor. Then `N` is a finite `R`-module: the images of a finite family of
`R₀`-generators of `H`, tensored with `m₁`, generate it. -/
theorem moduleFinite_of_tmul_span {R₀ R : Type u} [CommRing R₀] [CommRing R]
    {H M N : Type u} [AddCommGroup H] [Module R₀ H] [Module.Finite R₀ H]
    [AddCommGroup M] [Module R₀ M] [AddCommGroup N] [Module R N]
    (ψ : (H ⊗[R₀] M) →+ N) (hsurj : Function.Surjective ψ) (m₁ : M) (act : R → M → M)
    (hact : ∀ (c : R) (x : H) (m : M), ψ (x ⊗ₜ[R₀] act c m) = c • ψ (x ⊗ₜ[R₀] m))
    (hone : ∀ m : M, ∃ c : R, m = act c m₁) :
    Module.Finite R N := by
  classical
  obtain ⟨s, hs⟩ := Module.finite_def.1 (inferInstance : Module.Finite R₀ H)
  refine Module.finite_def.2 ⟨s.image fun x => ψ (x ⊗ₜ[R₀] m₁), eq_top_iff.2 ?_⟩
  have key : ∀ x : H, ψ (x ⊗ₜ[R₀] m₁) ∈
      Submodule.span R (((s.image fun x : H => ψ (x ⊗ₜ[R₀] m₁)) : Finset N) : Set N) := by
    intro x
    have hx : x ∈ Submodule.span R₀ (s : Set H) := hs ▸ Submodule.mem_top
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
    · intro z hz
      exact Submodule.subset_span
        (Finset.mem_coe.2 (Finset.mem_image_of_mem _ (Finset.mem_coe.1 hz)))
    · simp
    · intro z w _ _ hz hw
      rw [TensorProduct.add_tmul, map_add]
      exact Submodule.add_mem _ hz hw
    · intro a z _ hz
      obtain ⟨c, hc⟩ := hone (a • m₁)
      rw [TensorProduct.smul_tmul, hc, hact]
      exact Submodule.smul_mem _ _ hz
  have main : ∀ t : H ⊗[R₀] M, ψ t ∈
      Submodule.span R (((s.image fun x : H => ψ (x ⊗ₜ[R₀] m₁)) : Finset N) : Set N) := by
    intro t
    induction t with
    | tmul x m =>
        obtain ⟨c, hc⟩ := hone m
        rw [hc, hact]
        exact Submodule.smul_mem _ _ (key x)
    | add t₁ t₂ h₁ h₂ =>
        rw [map_add]
        exact Submodule.add_mem _ h₁ h₂
  intro y _
  obtain ⟨t, rfl⟩ := hsurj y
  exact main t

/-! ### Scalars through the affine base -/

/-- The structure map of the `R`-algebra of functions on an `R`-scheme, read off the structure
morphism at `⊤`. -/
theorem algebraMap_baseSectionsAlgebra_eq {R : Type u} [CommRing R] (W : Over (Spec (.of R))) :
    (algebraMap R Γ(W.left, ⊤) : R →+* Γ(W.left, ⊤)) =
      ((Scheme.ΓSpecIso (.of R)).inv ≫ W.hom.appTop).hom := by
  ext r
  have hres : ∀ s : Γ(W.left, ⊤),
      (W.left.ringCatSheaf.obj.map
        (TopologicalSpace.Opens.leTop (⊤ : W.left.Opens)).op).hom s = s := by
    intro s
    rw [show (TopologicalSpace.Opens.leTop (⊤ : W.left.Opens)).op =
        𝟙 (Opposite.op (⊤ : W.left.Opens)) from rfl, CategoryTheory.Functor.map_id]
    rfl
  show AlgebraicGeometry.baseRingToSections R W (Opposite.op ⊤) r = _
  exact hres _

/-- For a scheme over the spectrum of its affine base, the algebra map is the structure
morphism at `⊤`. -/
theorem algebraMap_over_isoSpec {Z S : Scheme.{u}} (q : Z ⟶ S) [IsAffine S] :
    (algebraMap (Γ(S, ⊤) : Type u) Γ((Over.mk (q ≫ S.isoSpec.hom)).left, ⊤)) = q.appTop.hom := by
  rw [algebraMap_baseSectionsAlgebra_eq (Over.mk (q ≫ S.isoSpec.hom)),
    show (Over.mk (q ≫ S.isoSpec.hom)).hom = q ≫ S.isoSpec.hom from rfl,
    ΓSpecIso_inv_comp_isoSpec_appTop q]

/-- The structure map from `Γ(Y, ⊤)` into the functions on `X`, via `f ≫ isoSpec`, is `f.appTop`
on elements. -/
private theorem ΓSpecIso_inv_comp_overMk_appTop_apply {Z S : Scheme.{u}} (q : Z ⟶ S) [IsAffine S]
    (c : (Γ(S, ⊤) : Type u)) :
    ((Scheme.ΓSpecIso (.of (Γ(S, ⊤) : Type u))).inv ≫
      (Over.mk (q ≫ S.isoSpec.hom) :
        Over (Spec (CommRingCat.of (Γ(S, ⊤) : Type u)))).hom.appTop).hom c = q.appTop.hom c :=
  congrArg (fun φ : Γ(S, ⊤) ⟶ Γ(Z, ⊤) => CommRingCat.Hom.hom φ c)
    (ΓSpecIso_inv_comp_isoSpec_appTop q)

/-! ### The situation of a morphism with vanishing higher direct images -/

section Situation

variable {X₀ Y₀ : Scheme.{u}} (g : X₀ ⟶ Y₀) [IsProper g] [IsAffine Y₀] (d : ℕ)
  (hvan : ∀ i : ℤ, (d : ℤ) < i → ∀ G : X₀.Modules, G.IsQuasicoherent →
      IsZero (((Scheme.Modules.pushforward g).rightDerivedPlus i).obj G))

/-- The top-degree base-change situation of `g` at the identity square. -/
def situation : TopDegreeBaseChangeSituation.{u} where
  X := X₀
  Y := Y₀
  f := g
  d := d
  isCompact_X := QuasiCompact.compactSpace_of_compactSpace g
  isQuasiSeparated_X := quasiSeparatedSpace_of_quasiSeparated g
  isCompact_Y := inferInstance
  isQuasiSeparated_Y := inferInstance
  vanishes_above := hvan
  X' := X₀
  Y' := Y₀
  g' := 𝟙 X₀
  f' := g
  g := 𝟙 Y₀
  isPullback := IsPullback.of_horiz_isIso ⟨by simp⟩

/-- The base `Y'` of `situation g d hvan` is affine. -/
instance isAffine_situation_Y' : IsAffine (situation g d hvan).Y' := ‹IsAffine Y₀›

/-- The affine base ring of `situation g d hvan` is `Γ(Y₀, ⊤)`. -/
theorem affineBaseRing_situation :
    (situation g d hvan).affineBaseRing = (Γ(Y₀, ⊤) : Type u) := rfl

/-- The affine base of `situation g d hvan` is `X₀` over `Spec Γ(Y₀, ⊤)` via
`g ≫ Y₀.isoSpec.hom`. -/
theorem affineBaseOver_situation :
    (situation g d hvan).affineBaseOver = Over.mk (g ≫ Y₀.isoSpec.hom) := rfl

variable (F₀ : X₀.Modules)

/-- A quasi-coherent module seen as an object of the quasi-coherent full subcategory. -/
def qcohObj {Z : Scheme.{u}} (G : Z.Modules) (hG : G.IsQuasicoherent) :
    (_root_.SheafOfModules.isQuasicoherent Z.ringCatSheaf).FullSubcategory := ⟨G, hG⟩

/-- The underlying module of `qcohObj G hG` is `G`. -/
@[simp] theorem qcohObj_obj {Z : Scheme.{u}} (G : Z.Modules) (hG : G.IsQuasicoherent) :
    (qcohObj G hG).obj = G := rfl

variable (hF₀ : F₀.IsQuasicoherent)

include hF₀ in
/-- The top-degree cohomology of `situation g d hvan` at `F₀` is `H ᵈ (X₀, F₀)`, viewed as a
`Γ(Y₀, ⊤)`-module by restriction of scalars along `g.appTop`. -/
theorem topDegreeCohomology_situation :
    (situation g d hvan).topDegreeCohomology (qcohObj F₀ hF₀) =
      (ModuleCat.restrictScalars g.appTop.hom).obj
        (((moduleGlobalSections X₀).rightDerived d).obj F₀) := by
  show (ModuleCat.restrictScalars
      (algebraMap (Γ(Y₀, ⊤) : Type u) Γ((Over.mk (g ≫ Y₀.isoSpec.hom)).left, ⊤))).obj
      (((moduleGlobalSections X₀).rightDerived d).obj F₀) = _
  rw [algebraMap_over_isoSpec g]

include hF₀ in
/-- For `Y₀` locally Noetherian and `F₀` coherent, the top-degree cohomology of
`situation g d hvan` at `F₀` is a finite module over the affine base ring. -/
theorem moduleFinite_topDegreeCohomology [IsLocallyNoetherian Y₀]
    [hc : _root_.SheafOfModules.IsCoherent F₀] :
    Module.Finite ((situation g d hvan).affineBaseRing)
      ((situation g d hvan).topDegreeCohomology (qcohObj F₀ hF₀)) := by
  rw [topDegreeCohomology_situation]
  exact AlgebraicGeometry.ProperCoherenceWitness.moduleFinite_cohomology g F₀ d

end Situation

/-- The structure sheaf of a scheme, as a module over itself. -/
def schemeUnit (Z : Scheme.{u}) : Z.Modules := _root_.SheafOfModules.unit Z.ringCatSheaf

/-- The structure sheaf `schemeUnit Z` is quasi-coherent. -/
instance isQuasicoherent_schemeUnit (Z : Scheme.{u}) : (schemeUnit Z).IsQuasicoherent :=
  Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit Z

/-- The identification `q^* 𝒪_S ≅ 𝒪_Z`, at the spelling of `schemeUnit`. -/
def pullbackUnit {Z S : Scheme.{u}} (q : Z ⟶ S) :
    (Scheme.Modules.pullback q).obj (schemeUnit S) ≅ schemeUnit Z :=
  Stacks.AlgebraicGeometry.AffineBaseChange.pullbackUnitIso q

/-! ### Transporting an endomorphism along a composite of isomorphisms -/

/-- An endomorphism commuting with an isomorphism commutes with its inverse. -/
theorem comm_inv {C : Type*} [Category C] {A B : C} (i : A ≅ B) {a : A ⟶ A} {b : B ⟶ B}
    (hc : a ≫ i.hom = i.hom ≫ b) : b ≫ i.inv = i.inv ≫ a := by
  rw [Iso.comp_inv_eq, Category.assoc, hc, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

/-- `comm_inv` with the forward morphism named, so that the identification of the forward
morphism of the isomorphism with it is checked once and explicitly. -/
theorem comm_inv' {C : Type*} [Category C] {A B : C} (i : A ≅ B) {w : A ⟶ B} (hw : i.hom = w)
    {a : A ⟶ A} {b : B ⟶ B} (hc : a ≫ w = w ≫ b) : b ≫ i.inv = i.inv ≫ a := by
  subst hw
  exact comm_inv i hc

/-- A functor carries a commutation relation to a commutation relation. -/
theorem map_comm {C D : Type*} [Category C] [Category D] (P : C ⥤ D) {A B : C} {e : A ⟶ B}
    {a : A ⟶ A} {b : B ⟶ B} (hc : a ≫ e = e ≫ b) :
    P.map a ≫ P.map e = P.map e ≫ P.map b := by
  rw [← P.map_comp, hc, P.map_comp]

/-- Two commutation relations compose. -/
theorem comp_comm {C : Type*} [Category C] {A B D : C} {e₁ : A ⟶ B} {e₂ : B ⟶ D}
    {a : A ⟶ A} {b : B ⟶ B} {c : D ⟶ D}
    (h₁ : a ≫ e₁ = e₁ ≫ b) (h₂ : b ≫ e₂ = e₂ ≫ c) :
    a ≫ (e₁ ≫ e₂) = (e₁ ≫ e₂) ≫ c := by
  rw [← Category.assoc, h₁, Category.assoc, h₂, Category.assoc]

/-! ### Multiplication by a global function along the comparison -/

open Stacks.AlgebraicGeometry.TopDegreeBaseChange in
/-- Pulling back along the structure morphism of an `R`-scheme is `R`-linear. -/
theorem pullback_map_smul_unit {R : Type u} [CommRing R] {Z : Scheme.{u}}
    (q : Z ⟶ Spec (.of R)) (r : R) (G : (Spec (.of R)).Modules) :
    letI : Linear R Z.Modules := AlgebraicGeometry.modulesLinear R (Over.mk q)
    letI : Linear R (Spec (CommRingCat.of R)).Modules :=
      AlgebraicGeometry.modulesLinear R (specBase R)
    (Scheme.Modules.pullback q).map (r • 𝟙 G) =
      r • 𝟙 ((Scheme.Modules.pullback q).obj G) := by
  let : Linear R Z.Modules := AlgebraicGeometry.modulesLinear R (Over.mk q)
  let : Linear R (Spec (CommRingCat.of R)).Modules :=
    AlgebraicGeometry.modulesLinear R (specBase R)
  let : (Scheme.Modules.pullback q).Linear R :=
    AlgebraicGeometry.over_pullback_linear R (toSpecBase R (Over.mk q))
  rw [Functor.map_smul, CategoryTheory.Functor.map_id]

/-- In a linear category, multiplication by a scalar commutes with every morphism. -/
theorem smul_id_comp {C : Type*} [Category C] [Preadditive C] {R : Type*} [CommRing R]
    [Linear R C] (r : R) {A B : C} (ψ : A ⟶ B) : (r • 𝟙 A) ≫ ψ = ψ ≫ (r • 𝟙 B) := by
  rw [Linear.smul_comp, Linear.comp_smul, Category.id_comp, Category.comp_id]

/-- The structure sheaf of `Spec S` is the module `S` over itself, read as a sheaf. -/
def unitTildeIso (S : CommRingCat.{u}) :
    schemeUnit (Spec S) ≅ (tilde.functor S).obj (ModuleCat.of S S) :=
  (tildeSelf (R := S)).symm

/-- **The direct image of the structure sheaf along `Spec φ`** is the sheaf associated with the
target ring, its scalars restricted along `φ`. -/
def pushforwardUnitTilde {R₀ S : CommRingCat.{u}} (φ : R₀ ⟶ S) :
    (Scheme.Modules.pushforward (Spec.map φ)).obj (schemeUnit (Spec S)) ≅
      (tilde.functor R₀).obj ((ModuleCat.restrictScalars φ.hom).obj (ModuleCat.of S S)) :=
  (Scheme.Modules.pushforward (Spec.map φ)).mapIso (unitTildeIso S) ≪≫
    (pushforwardTildeIso R₀ S φ).app (ModuleCat.of S S)

open Stacks.AlgebraicGeometry.TopDegreeBaseChange in
/-- **The identification of `(Spec φ)_* 𝒪` with a tilde carries multiplication by a function on
the source to multiplication on the module.** -/
theorem pushforwardUnitTilde_smul {R₀ S : CommRingCat.{u}} (φ : R₀ ⟶ S) (r : (S : Type u)) :
    letI : Linear (S : Type u) (Spec S).Modules :=
      AlgebraicGeometry.modulesLinear (S : Type u) (specBase (S : Type u))
    (Scheme.Modules.pushforward (Spec.map φ)).map (r • 𝟙 (schemeUnit (Spec S))) ≫
        (pushforwardUnitTilde φ).hom =
      (pushforwardUnitTilde φ).hom ≫
        (tilde.functor R₀).map
          ((ModuleCat.restrictScalars φ.hom).map (r • 𝟙 (ModuleCat.of S S))) := by
  let : Linear (S : Type u) (Spec S).Modules :=
    AlgebraicGeometry.modulesLinear (S : Type u) (specBase (S : Type u))
  let : (tilde.functor S).Linear (S : Type u) := linear_tildeFunctor (S : Type u)
  have hsmul : (tilde.functor S).map (r • 𝟙 (ModuleCat.of S S)) =
      r • 𝟙 ((tilde.functor S).obj (ModuleCat.of S S)) := by
    rw [Functor.map_smul, CategoryTheory.Functor.map_id]
  have hdef : (pushforwardUnitTilde φ).hom =
      (Scheme.Modules.pushforward (Spec.map φ)).map (unitTildeIso S).hom ≫
        (pushforwardTildeIso R₀ S φ).hom.app (ModuleCat.of S S) := rfl
  rw [hdef, ← Category.assoc, ← CategoryTheory.Functor.map_comp,
    smul_id_comp r (unitTildeIso S).hom, ← hsmul, CategoryTheory.Functor.map_comp]
  simp only [Category.assoc]
  exact congrArg _ ((pushforwardTildeIso R₀ S φ).hom.naturality (r • 𝟙 (ModuleCat.of S S)))

/-- **The bifunctor of [Stacks, Tag 01CA] on a pair whose second component is an identity is
the flipped functor's map.** Over a bare pair of categories, where there is nothing to unfold.

This was invisible while the uncurried bifunctor had a reducible name: a goal about
`Functor.uncurry.obj` and a hypothesis about `Functor.flip.obj` differ by one `Functor.map_id`,
and the unifier used to be allowed to find it. Both shapes occur in this file's chain —
`Stacks.AffineProjectionFormula.projectionFormulaMap_natural` is stated at the uncurried
bifunctor, `Stacks.SheafOfModules.TensorPower.tensorLeftIsoTensorRight` at the flipped one — so
the step is taken once here. -/
private theorem uncurry_map_id_right {A : Type*} [Category A] {B : Type*} [Category B]
    {E : Type*} [Category E] (T : A ⥤ B ⥤ E) {M M' : A} (f : M ⟶ M') (N : B) :
    (Functor.uncurry.obj T).map (X := (M, N)) (Y := (M', N)) (f, 𝟙 N) = (T.flip.obj N).map f := by
  simp

/-- **Multiplying the left factor of a tensor product by a base scalar is multiplication by
that scalar.** The right-hand tensoring functor is `R`-linear, by the symmetry of the tensor
product. -/
theorem tensorSheaf_map_smul_left {R : Type u} [CommRing R] (W : Over (Spec (.of R)))
    (M B : W.left.Modules) (r : R) :
    letI : Linear R W.left.Modules := AlgebraicGeometry.modulesLinear R W
    (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨W.left.toRingedSpace.presheaf, W.left.toRingedSpace.IsSheaf⟩)).map
        (X := (M, B)) (Y := (M, B)) ((r • 𝟙 M), 𝟙 B) =
      r • 𝟙 (show W.left.Modules from
        ((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨W.left.toRingedSpace.presheaf, W.left.toRingedSpace.IsSheaf⟩).obj M).obj B) := by
  let : Linear R W.left.Modules := AlgebraicGeometry.modulesLinear R W
  let : Linear R (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        ⟨W.left.toRingedSpace.presheaf, W.left.toRingedSpace.IsSheaf⟩)) :=
    Linear.ofRingMorphism (AlgebraicGeometry.baseRingToCenter R W)
  let hlin : ((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨W.left.toRingedSpace.presheaf, W.left.toRingedSpace.IsSheaf⟩).flip.obj B).Linear R :=
    AlgebraicGeometry.CoherentModuleFunctors.tensorRight_linear R W B
  exact (uncurry_map_id_right _ (r • 𝟙 M) B).trans
    ((hlin.map_smul (𝟙 M) r).trans (congrArg (fun z => r • z)
      (CategoryTheory.Functor.map_id
        ((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨W.left.toRingedSpace.presheaf, W.left.toRingedSpace.IsSheaf⟩).flip.obj B) M)))

/-! ### The base-change square over the spectrum of the affine base -/

section BaseChange

open Stacks.AlgebraicGeometry.AffineBaseChange
open Stacks.AlgebraicGeometry.AffinePushforward

variable {X₀ Y₀ X Y : Scheme.{u}} [IsAffine Y₀] [IsAffine Y]
  (g : X₀ ⟶ Y₀) (h : X ⟶ X₀) (f : X ⟶ Y) (u : Y ⟶ Y₀) (sq : IsPullback h f g u)

include sq in
/-- The cartesian square of `sq` read over `Spec Γ(Y₀, ⊤)`. -/
theorem isPullback_specSquare :
    IsPullback (f ≫ Y.isoSpec.hom) h (Spec.map u.appTop) (g ≫ Y₀.isoSpec.hom) :=
  sq.flip.paste_horiz (IsPullback.of_horiz_isIso ⟨Scheme.isoSpec_hom_naturality u⟩)

/-- The ring of functions on `Y`, as a module over the functions on `Y₀`. -/
abbrev baseModule : ModuleCat.{u} (Γ(Y₀, ⊤) : CommRingCat.{u}) :=
  (ModuleCat.restrictScalars (u.appTop).hom).obj (ModuleCat.of Γ(Y, ⊤) Γ(Y, ⊤))

include sq in
/-- **The direct image of the structure sheaf of the base change** is the pullback to `X₀` of the
sheaf on `Spec Γ(Y₀, ⊤)` associated with `Γ(Y, ⊤)`. -/
def pushforwardUnitIsoPullbackTilde :
    (Scheme.Modules.pushforward h).obj (schemeUnit X) ≅
      (Scheme.Modules.pullback (g ≫ Y₀.isoSpec.hom)).obj
        ((tilde.functor Γ(Y₀, ⊤)).obj (baseModule u)) :=
  haveI : IsAffineHom h := MorphismProperty.of_isPullback sq.flip inferInstance
  haveI := AffineBaseChangeIso.isIso_baseChangeNatTrans_of_isAffineHom
    (isPullback_specSquare g h f u sq) (schemeUnit (Spec Γ(Y, ⊤)))
  ((Scheme.Modules.pushforward h).mapIso (pullbackUnit (f ≫ Y.isoSpec.hom))).symm ≪≫
    ((asIso ((baseChangeNatTrans (isPullback_specSquare g h f u sq).w).app
        (schemeUnit (Spec Γ(Y, ⊤))))).symm ≪≫
      (Scheme.Modules.pullback (g ≫ Y₀.isoSpec.hom)).mapIso (pushforwardUnitTilde (u.appTop)))

open Stacks.AlgebraicGeometry.TopDegreeBaseChange in
include sq in
/-- **The comparison of `pushforwardUnitIsoPullbackTilde` carries multiplication by a function
pulled back from `Y` to multiplication on the module `Γ(Y, ⊤)`.** -/
theorem pushforwardUnitIsoPullbackTilde_smul (r : (Γ(Y, ⊤) : Type u)) :
    letI : Linear (Γ(Y, ⊤) : Type u) X.Modules :=
      AlgebraicGeometry.modulesLinear (Γ(Y, ⊤) : Type u)
        (Over.mk (f ≫ Y.isoSpec.hom) : Over (Spec (CommRingCat.of (Γ(Y, ⊤) : Type u))))
    (Scheme.Modules.pushforward h).map (r • 𝟙 (schemeUnit X)) ≫
        (pushforwardUnitIsoPullbackTilde g h f u sq).hom =
      (pushforwardUnitIsoPullbackTilde g h f u sq).hom ≫
        (Scheme.Modules.pullback (g ≫ Y₀.isoSpec.hom)).map
          ((tilde.functor Γ(Y₀, ⊤)).map
            ((ModuleCat.restrictScalars (u.appTop).hom).map
              (r • 𝟙 (ModuleCat.of Γ(Y, ⊤) Γ(Y, ⊤))))) := by
  have : IsAffineHom h := MorphismProperty.of_isPullback sq.flip inferInstance
  have := AffineBaseChangeIso.isIso_baseChangeNatTrans_of_isAffineHom
    (isPullback_specSquare g h f u sq) (schemeUnit (Spec Γ(Y, ⊤)))
  let : Linear (Γ(Y, ⊤) : Type u) X.Modules :=
    AlgebraicGeometry.modulesLinear (Γ(Y, ⊤) : Type u)
      (Over.mk (f ≫ Y.isoSpec.hom) : Over (Spec (CommRingCat.of (Γ(Y, ⊤) : Type u))))
  let : Linear (Γ(Y, ⊤) : Type u) (Spec (CommRingCat.of (Γ(Y, ⊤) : Type u))).Modules :=
    AlgebraicGeometry.modulesLinear (Γ(Y, ⊤) : Type u) (specBase (Γ(Y, ⊤) : Type u))
  have step0 : (Scheme.Modules.pullback (f ≫ Y.isoSpec.hom)).map
        (r • 𝟙 (schemeUnit (Spec Γ(Y, ⊤)))) ≫ (pullbackUnit (f ≫ Y.isoSpec.hom)).hom =
      (pullbackUnit (f ≫ Y.isoSpec.hom)).hom ≫ (r • 𝟙 (schemeUnit X)) := by
    rw [pullback_map_smul_unit (R := (Γ(Y, ⊤) : Type u)) (f ≫ Y.isoSpec.hom) r
      (schemeUnit (Spec Γ(Y, ⊤)))]
    exact smul_id_comp r _
  have step1 := map_comm (Scheme.Modules.pushforward h)
    (comm_inv (pullbackUnit (f ≫ Y.isoSpec.hom)) step0)
  have step2 := comm_inv (asIso ((baseChangeNatTrans (isPullback_specSquare g h f u sq).w).app
      (schemeUnit (Spec Γ(Y, ⊤)))))
    ((baseChangeNatTrans (isPullback_specSquare g h f u sq).w).naturality
      (r • 𝟙 (schemeUnit (Spec Γ(Y, ⊤)))))
  have step3 := map_comm (Scheme.Modules.pullback (g ≫ Y₀.isoSpec.hom))
    (pushforwardUnitTilde_smul (u.appTop) r)
  exact comp_comm step1 (comp_comm step2 step3)

end BaseChange

/-! ### Cohomology along the affine morphism `h` -/

section Cohomology

open Stacks.Cohomology.AffineComparison

variable {X₀ X Y : Scheme.{u}} [IsAffine Y] (h : X ⟶ X₀) (f : X ⟶ Y) [IsAffineHom h]
  (F : X.Modules) [F.IsQuasicoherent] (d : ℕ)

open Stacks.AlgebraicGeometry.TopDegreeBaseChange in
/-- **[Stacks, Tag 089W] carries multiplication by a function pulled back from `Y`.** -/
theorem cohomologyIsoPushforward_smul_appTop (r : (Γ(Y, ⊤) : Type u))
    (z : ((((moduleGlobalSections X).rightDerived d).obj F) : Type u)) :
    letI : Linear (Γ(Y, ⊤) : Type u) X.Modules :=
      AlgebraicGeometry.modulesLinear (Γ(Y, ⊤) : Type u)
        (Over.mk (f ≫ Y.isoSpec.hom) : Over (Spec (CommRingCat.of (Γ(Y, ⊤) : Type u))))
    (cohomologyIsoPushforward h F d).hom.hom ((f.appTop).hom r • z) =
      (((moduleGlobalSections X₀).rightDerived d).map
        ((Scheme.Modules.pushforward h).map (r • 𝟙 F))).hom
          ((cohomologyIsoPushforward h F d).hom.hom z) := by
  let : Linear (Γ(Y, ⊤) : Type u) X.Modules :=
    AlgebraicGeometry.modulesLinear (Γ(Y, ⊤) : Type u)
      (Over.mk (f ≫ Y.isoSpec.hom) : Over (Spec (CommRingCat.of (Γ(Y, ⊤) : Type u))))
  have h1 := cohomologyIsoPushforward_baseSmul
    (R := (Γ(Y, ⊤) : Type u))
    (Y := (Over.mk (f ≫ Y.isoSpec.hom) : Over (Spec (CommRingCat.of (Γ(Y, ⊤) : Type u)))))
    h F d r z
  rw [← ΓSpecIso_inv_comp_overMk_appTop_apply f r]
  exact h1

end Cohomology

/-! ### The direct image of the base-changed module as a value of the geometric factor -/

section TensorComparison

open Stacks.AlgebraicGeometry.AffineBaseChange
open Stacks.AlgebraicGeometry.AffinePushforward
open Stacks.AlgebraicGeometry.DerivedAffinePushforward
open Stacks.AlgebraicGeometry.ProjectionFormula
open Stacks.SheafOfModules.TensorPower

variable {X₀ Y₀ X Y : Scheme.{u}} [IsAffine Y₀] [IsAffine Y]
  (g : X₀ ⟶ Y₀) (h : X ⟶ X₀) (f : X ⟶ Y) (u : Y ⟶ Y₀) (sq : IsPullback h f g u)
  (F₀ : X₀.Modules) (hF₀ : F₀.IsQuasicoherent) (F : X.Modules)
  (e : F ≅ (Scheme.Modules.pullback h).obj F₀)

/-- **The projection formula at the structure sheaf**, `h_* 𝒪_X ⊗ F₀ ≅ h_*(h^* F₀)`, for
quasi-coherent `F₀`, stated with `schemeUnit`. -/
def pushforwardUnitTensorIso [IsAffineHom h] (F₀ : X₀.Modules) (hF₀ : F₀.IsQuasicoherent) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨X₀.toRingedSpace.presheaf, X₀.toRingedSpace.IsSheaf⟩).obj
        ((Scheme.Modules.pushforward h).obj (schemeUnit X))).obj F₀ ≅
      (Scheme.Modules.pushforward h).obj ((Scheme.Modules.pullback h).obj F₀) :=
  projectionFormulaIsoOfQuasicoherent h (schemeUnit X) F₀
      (isQuasicoherent_schemeUnit X) hF₀ ≪≫
    (Scheme.Modules.pushforward h).mapIso
      (Stacks.RingedSpace.tensorSheafUnitLeftIso X.toRingedSpace
        ((Scheme.Modules.pullback h).obj F₀))

/-- The forward morphism of `pushforwardUnitTensorIso` is `projectionFormulaMap` followed by the
pushforward of the left unitor of the tensor product. -/
theorem pushforwardUnitTensorIso_hom [IsAffineHom h] (F₀ : X₀.Modules)
    (hF₀ : F₀.IsQuasicoherent) :
    (pushforwardUnitTensorIso h F₀ hF₀).hom =
      projectionFormulaMap h (schemeUnit X) F₀ ≫
        (Scheme.Modules.pushforward h).map
          (Stacks.RingedSpace.tensorSheafUnitLeftIso X.toRingedSpace
            ((Scheme.Modules.pullback h).obj F₀)).hom :=
  have := isIso_projectionFormulaMap h (schemeUnit X) F₀ (isQuasicoherent_schemeUnit X) hF₀
  rfl

include sq hF₀ e in
/-- **The direct image along `h` of the base change of `F₀` is the value at `Γ(Y, ⊤)` of the
geometric factor `M ↦ F₀ ⊗ (g ≫ isoSpec)^* M~` of [Stacks, Tag 0EX3] (b).** -/
def pushforwardIsoTensorTilde :
    (Scheme.Modules.pushforward h).obj F ≅
      ((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨X₀.toRingedSpace.presheaf, X₀.toRingedSpace.IsSheaf⟩).obj F₀).obj
        ((Scheme.Modules.pullback (g ≫ Y₀.isoSpec.hom)).obj
          ((tilde.functor Γ(Y₀, ⊤)).obj (baseModule u))) :=
  haveI : IsAffineHom h := MorphismProperty.of_isPullback sq.flip inferInstance
  (Scheme.Modules.pushforward h).mapIso e ≪≫
    ((pushforwardUnitTensorIso h F₀ hF₀).symm ≪≫
      (((tensorLeftIsoTensorRight X₀.toRingedSpace.presheaf X₀.ringCatSheaf.2 F₀).app
          ((Scheme.Modules.pushforward h).obj (schemeUnit X))).symm ≪≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨X₀.toRingedSpace.presheaf, X₀.toRingedSpace.IsSheaf⟩).obj F₀).mapIso
          (pushforwardUnitIsoPullbackTilde g h f u sq)))

open Stacks.AlgebraicGeometry.TopDegreeBaseChange in
include sq hF₀ e in
/-- **The comparison carries multiplication by a function pulled back from `Y` to the tilde of
multiplication on `Γ(Y, ⊤)`.** -/
theorem pushforwardIsoTensorTilde_smul (r : (Γ(Y, ⊤) : Type u)) :
    letI : Linear (Γ(Y, ⊤) : Type u) X.Modules :=
      AlgebraicGeometry.modulesLinear (Γ(Y, ⊤) : Type u)
        (Over.mk (f ≫ Y.isoSpec.hom) : Over (Spec (CommRingCat.of (Γ(Y, ⊤) : Type u))))
    (Scheme.Modules.pushforward h).map (r • 𝟙 F) ≫
        (pushforwardIsoTensorTilde g h f u sq F₀ hF₀ F e).hom =
      (pushforwardIsoTensorTilde g h f u sq F₀ hF₀ F e).hom ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨X₀.toRingedSpace.presheaf, X₀.toRingedSpace.IsSheaf⟩).obj F₀).map
          ((Scheme.Modules.pullback (g ≫ Y₀.isoSpec.hom)).map
            ((tilde.functor Γ(Y₀, ⊤)).map
              ((ModuleCat.restrictScalars (u.appTop).hom).map
                (r • 𝟙 (ModuleCat.of Γ(Y, ⊤) Γ(Y, ⊤)))))) := by
  have : IsAffineHom h := MorphismProperty.of_isPullback sq.flip inferInstance
  let : Linear (Γ(Y, ⊤) : Type u) X.Modules :=
    AlgebraicGeometry.modulesLinear (Γ(Y, ⊤) : Type u)
      (Over.mk (f ≫ Y.isoSpec.hom) : Over (Spec (CommRingCat.of (Γ(Y, ⊤) : Type u))))
  let : Linear (Γ(Y, ⊤) : Type u)
      (SheafOfModules.{u} (Stacks.RingedSpace.structureRingSheaf X.toRingedSpace)) :=
    AlgebraicGeometry.modulesLinear (Γ(Y, ⊤) : Type u)
      (Over.mk (f ≫ Y.isoSpec.hom) : Over (Spec (CommRingCat.of (Γ(Y, ⊤) : Type u))))
  let : Linear (Γ(Y, ⊤) : Type u)
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
        ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩)) :=
    AlgebraicGeometry.modulesLinear (Γ(Y, ⊤) : Type u)
      (Over.mk (f ≫ Y.isoSpec.hom) : Over (Spec (CommRingCat.of (Γ(Y, ⊤) : Type u))))
  have hpfiso := isIso_projectionFormulaMap h (schemeUnit X) F₀
    (isQuasicoherent_schemeUnit X) hF₀
  have s1 := map_comm (Scheme.Modules.pushforward h) (smul_id_comp r e.hom)
  have t1 := projectionFormulaMap_natural h (r • 𝟙 (schemeUnit X)) (𝟙 F₀)
  have t2 : (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩)).map
        (X := (schemeUnit X,
          (RingedSpaceModuleAdjunction.modulePullback h.toLRSHom.toShHom).obj F₀))
        (Y := (schemeUnit X,
          (RingedSpaceModuleAdjunction.modulePullback h.toLRSHom.toShHom).obj F₀))
        (r • 𝟙 (schemeUnit X),
          (RingedSpaceModuleAdjunction.modulePullback h.toLRSHom.toShHom).map (𝟙 F₀)) =
      r • 𝟙 (show X.Modules from
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj (schemeUnit X)).obj
          ((Scheme.Modules.pullback h).obj F₀)) :=
    (congrArg (fun ψ => (Functor.uncurry.obj
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩)).map
        (X := (schemeUnit X,
          (RingedSpaceModuleAdjunction.modulePullback h.toLRSHom.toShHom).obj F₀))
        (Y := (schemeUnit X,
          (RingedSpaceModuleAdjunction.modulePullback h.toLRSHom.toShHom).obj F₀))
        (r • 𝟙 (schemeUnit X), ψ)) (CategoryTheory.Functor.map_id _ F₀)).trans
      (tensorSheaf_map_smul_left
        (Over.mk (f ≫ Y.isoSpec.hom) : Over (Spec (CommRingCat.of (Γ(Y, ⊤) : Type u))))
        (schemeUnit X) ((Scheme.Modules.pullback h).obj F₀) r)
  rw [t2] at t1
  have t3 := map_comm (Scheme.Modules.pushforward h)
    (smul_id_comp r (Stacks.RingedSpace.tensorSheafUnitLeftIso X.toRingedSpace
      ((Scheme.Modules.pullback h).obj F₀)).hom)
  have s2 := comm_inv' (pushforwardUnitTensorIso h F₀ hF₀)
    (pushforwardUnitTensorIso_hom h F₀ hF₀) (comp_comm t1 t3)
  have s3 := comm_inv ((tensorLeftIsoTensorRight X₀.toRingedSpace.presheaf X₀.ringCatSheaf.2 F₀).app
      ((Scheme.Modules.pushforward h).obj (schemeUnit X)))
    ((tensorLeftIsoTensorRight X₀.toRingedSpace.presheaf X₀.ringCatSheaf.2 F₀).hom.naturality
      ((Scheme.Modules.pushforward h).map (r • 𝟙 (schemeUnit X))))
  have s4 := map_comm ((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨X₀.toRingedSpace.presheaf, X₀.toRingedSpace.IsSheaf⟩).obj F₀)
    (pushforwardUnitIsoPullbackTilde_smul g h f u sq r)
  have s3' := (congrArg (· ≫ ((tensorLeftIsoTensorRight X₀.toRingedSpace.presheaf
        X₀.ringCatSheaf.2 F₀).app ((Scheme.Modules.pushforward h).obj (schemeUnit X))).inv)
      (uncurry_map_id_right (Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨X₀.toRingedSpace.presheaf, X₀.toRingedSpace.IsSheaf⟩)
        ((Scheme.Modules.pushforward h).map (r • 𝟙 (schemeUnit X))) F₀)).trans s3
  exact comp_comm s1 (comp_comm s2 (comp_comm s3' s4))

end TensorComparison

/-! ### The last paragraph of the proof of Tag 0EX4 -/

section Comparison

open scoped TensorProduct
open Stacks.Cohomology.AffineComparison
open Stacks.AlgebraicGeometry.TopDegreeBaseChange
open Stacks.SheafOfModules.TensorPower

variable {X₀ Y₀ X Y : Scheme.{u}} (g : X₀ ⟶ Y₀) [IsProper g] [IsAffine Y₀] (d : ℕ)
  (hvan : ∀ i : ℤ, (d : ℤ) < i → ∀ G : X₀.Modules, G.IsQuasicoherent →
    IsZero (((Scheme.Modules.pushforward g).rightDerivedPlus i).obj G))
  (F₀ : X₀.Modules) (hF₀ : F₀.IsQuasicoherent)
  [IsAffine Y] (h : X ⟶ X₀) [IsAffineHom h] (f : X ⟶ Y) (u : Y ⟶ Y₀)
  (sq : IsPullback h f g u) (F : X.Modules) [F.IsQuasicoherent]
  (e : F ≅ (Scheme.Modules.pullback h).obj F₀)

include hvan sq hF₀ e in
/-- **The comparison of the last paragraph of [Stacks, Tag 0EX4]**: the degree-`d` cohomology of
the base change, read over the affine base ring, is `H ᵈ (X₀, F₀) ⊗ Γ(Y, ⊤)`. -/
def baseChangeTensorIso :
    (MonoidalCategory.tensorLeft
        ((situation g d hvan).topDegreeCohomology (qcohObj F₀ hF₀))).obj (baseModule u) ≅
      (ModuleCat.restrictScalars
            (algebraMap ((situation g d hvan).affineBaseRing)
              Γ(((situation g d hvan).affineBaseOver).left, ⊤))).obj
        ((ModuleCat.restrictScalars h.appTop.hom).obj
          (((moduleGlobalSections X).rightDerived d).obj F)) :=
  ((situation g d hvan).topDegreeTensorCohomologyIso (qcohObj F₀ hF₀)).app (baseModule u) ≪≫
    (ModuleCat.restrictScalars
        (algebraMap ((situation g d hvan).affineBaseRing)
          Γ(((situation g d hvan).affineBaseOver).left, ⊤))).mapIso
      ((((moduleGlobalSections X₀).rightDerived d).mapIso
          (pushforwardIsoTensorTilde g h f u sq F₀ hF₀ F e).symm) ≪≫
        (cohomologyIsoPushforward h F d).symm)

include hvan sq hF₀ e in
/-- The forward morphism of `baseChangeTensorIso`, written as the composite of its defining
isomorphisms. -/
theorem baseChangeTensorIso_hom :
    (baseChangeTensorIso g d hvan F₀ hF₀ h f u sq F e).hom =
      ((situation g d hvan).topDegreeTensorCohomologyIso
          (qcohObj F₀ hF₀)).hom.app (baseModule u) ≫
        (ModuleCat.restrictScalars
            (algebraMap ((situation g d hvan).affineBaseRing)
              Γ(((situation g d hvan).affineBaseOver).left, ⊤))).map
          ((((moduleGlobalSections X₀).rightDerived d).map
              (pushforwardIsoTensorTilde g h f u sq F₀ hF₀ F e).inv) ≫
            (cohomologyIsoPushforward h F d).inv) := rfl

open Stacks.AlgebraicGeometry.TopDegreeBaseChange in
include hvan sq hF₀ e in
/-- **The comparison carries multiplication by a function pulled back from `Y`.** -/
theorem baseChangeTensorIso_smul (c : (Γ(Y, ⊤) : Type u)) :
    letI : Linear (Γ(Y, ⊤) : Type u) X.Modules :=
      AlgebraicGeometry.modulesLinear (Γ(Y, ⊤) : Type u)
        (Over.mk (f ≫ Y.isoSpec.hom) : Over (Spec (CommRingCat.of (Γ(Y, ⊤) : Type u))))
    (MonoidalCategory.tensorLeft
          ((situation g d hvan).topDegreeCohomology (qcohObj F₀ hF₀))).map
          ((ModuleCat.restrictScalars (u.appTop).hom).map
            (c • 𝟙 (ModuleCat.of Γ(Y, ⊤) Γ(Y, ⊤)))) ≫
        (baseChangeTensorIso g d hvan F₀ hF₀ h f u sq F e).hom =
      (baseChangeTensorIso g d hvan F₀ hF₀ h f u sq F e).hom ≫
        (ModuleCat.restrictScalars
            (algebraMap ((situation g d hvan).affineBaseRing)
              Γ(((situation g d hvan).affineBaseOver).left, ⊤))).map
          ((ModuleCat.restrictScalars h.appTop.hom).map
            (((moduleGlobalSections X).rightDerived d).map (c • 𝟙 F))) := by
  let : Linear (Γ(Y, ⊤) : Type u) X.Modules :=
    AlgebraicGeometry.modulesLinear (Γ(Y, ⊤) : Type u)
      (Over.mk (f ≫ Y.isoSpec.hom) : Over (Spec (CommRingCat.of (Γ(Y, ⊤) : Type u))))
  rw [baseChangeTensorIso_hom]
  exact comp_comm
    (((situation g d hvan).topDegreeTensorCohomologyIso (qcohObj F₀ hF₀)).hom.naturality
      ((ModuleCat.restrictScalars (u.appTop).hom).map
        (c • 𝟙 (ModuleCat.of Γ(Y, ⊤) Γ(Y, ⊤)))))
    (map_comm (ModuleCat.restrictScalars
        (algebraMap ((situation g d hvan).affineBaseRing)
          Γ(((situation g d hvan).affineBaseOver).left, ⊤)))
      (comp_comm
        (map_comm ((moduleGlobalSections X₀).rightDerived d)
          (comm_inv (pushforwardIsoTensorTilde g h f u sq F₀ hF₀ F e)
            (pushforwardIsoTensorTilde_smul g h f u sq F₀ hF₀ F e c)))
        (comm_inv (cohomologyIsoPushforward h F d)
          (cohomologyIsoPushforward_naturality h (c • 𝟙 F) d))))

end Comparison

section Main

open scoped TensorProduct
open Stacks.Cohomology.AffineComparison
open Stacks.AlgebraicGeometry.TopDegreeBaseChange

variable {X₀ Y₀ X Y : Scheme.{u}} (g : X₀ ⟶ Y₀) [IsProper g] [IsAffine Y₀]
  [IsLocallyNoetherian Y₀] (d : ℕ)
  (hvan : ∀ i : ℤ, (d : ℤ) < i → ∀ G : X₀.Modules, G.IsQuasicoherent →
    IsZero (((Scheme.Modules.pushforward g).rightDerivedPlus i).obj G))
  (F₀ : X₀.Modules) (hF₀ : F₀.IsQuasicoherent)
  [IsAffine Y] (h : X ⟶ X₀) (f : X ⟶ Y) (u : Y ⟶ Y₀) (sq : IsPullback h f g u)
  (F : X.Modules) (e : F ≅ (Scheme.Modules.pullback h).obj F₀)

include hvan sq hF₀ e in
/-- **The last paragraph of the proof of [Stacks, Tag 0EX4].** Let `g : X₀ ⟶ Y₀` be proper onto
an affine locally Noetherian base with higher direct images vanishing above `d`, let `F₀` be
quasi-coherent and coherent, and let `u : Y ⟶ Y₀` be any morphism from an affine scheme. Then
for the base change `X = X₀ ×_{Y₀} Y` and `F = h^* F₀`, the module `H ᵈ (X, F)` is a finite
`Γ(Y, ⊤)`-module. -/
theorem moduleFinite_cohomology_of_isPullback_of_isQuasicoherent
    [_root_.SheafOfModules.IsCoherent F₀] :
    Module.Finite Γ(Y, ⊤) ((ModuleCat.restrictScalars f.appTop.hom).obj
      (((moduleGlobalSections X).rightDerived d).obj F)) := by
  have : IsAffineHom h := MorphismProperty.of_isPullback sq.flip inferInstance
  have : ((Scheme.Modules.pullback h).obj F₀).IsQuasicoherent :=
    @AlgebraicGeometry.SheafOfModules.modulePullback_isQuasicoherent _ _
      h.toLRSHom.toShHom _ hF₀
  have : F.IsQuasicoherent :=
    (_root_.SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso e.symm inferInstance
  let : Linear (Γ(Y, ⊤) : Type u) X.Modules :=
    AlgebraicGeometry.modulesLinear (Γ(Y, ⊤) : Type u)
      (Over.mk (f ≫ Y.isoSpec.hom) : Over (Spec (CommRingCat.of (Γ(Y, ⊤) : Type u))))
  have := moduleFinite_topDegreeCohomology g d hvan F₀ hF₀
  refine moduleFinite_of_tmul_span
    (baseChangeTensorIso g d hvan F₀ hF₀ h f u sq F e).hom.hom.toAddMonoidHom ?_
    (1 : (Γ(Y, ⊤) : Type u))
    (@HMul.hMul (Γ(Y, ⊤) : Type u) (Γ(Y, ⊤) : Type u) (Γ(Y, ⊤) : Type u) _) ?_
    (fun m => ⟨m, Eq.symm (@mul_one (Γ(Y, ⊤) : Type u) _ m)⟩)
  · intro y
    refine ⟨(baseChangeTensorIso g d hvan F₀ hF₀ h f u sq F e).inv.hom y, ?_⟩
    exact DFunLike.congr_fun (congrArg ModuleCat.Hom.hom
      (baseChangeTensorIso g d hvan F₀ hF₀ h f u sq F e).inv_hom_id) y
  · intro c x m
    have happ := DFunLike.congr_fun
      (congrArg ModuleCat.Hom.hom (baseChangeTensorIso_smul g d hvan F₀ hF₀ h f u sq F e c))
      (x ⊗ₜ[(situation g d hvan).affineBaseRing] m)
    have hsm := (rightDerived_map_baseSmul_hom
        (Over.mk (f ≫ Y.isoSpec.hom) : Over (Spec (CommRingCat.of (Γ(Y, ⊤) : Type u))))
        F d c (show ((((moduleGlobalSections X).rightDerived d).obj F) : Type u) from
          (baseChangeTensorIso g d hvan F₀ hF₀ h f u sq F e).hom.hom
            (x ⊗ₜ[(situation g d hvan).affineBaseRing] m))).trans
      (congrArg (fun t : (Γ(X, ⊤) : Type u) =>
        t • (show ((((moduleGlobalSections X).rightDerived d).obj F) : Type u) from
          (baseChangeTensorIso g d hvan F₀ hF₀ h f u sq F e).hom.hom
            (x ⊗ₜ[(situation g d hvan).affineBaseRing] m)))
        (ΓSpecIso_inv_comp_overMk_appTop_apply f c))
    have hres₁ := ModuleCat.restrictScalars.map_apply
      (algebraMap ((situation g d hvan).affineBaseRing)
        Γ(((situation g d hvan).affineBaseOver).left, ⊤))
      ((ModuleCat.restrictScalars h.appTop.hom).map
        (((moduleGlobalSections X).rightDerived d).map (c • 𝟙 F)))
      ((baseChangeTensorIso g d hvan F₀ hF₀ h f u sq F e).hom.hom
        (x ⊗ₜ[(situation g d hvan).affineBaseRing] m))
    have hres₂ := ModuleCat.restrictScalars.map_apply h.appTop.hom
      (((moduleGlobalSections X).rightDerived d).map (c • 𝟙 F))
      ((baseChangeTensorIso g d hvan F₀ hF₀ h f u sq F e).hom.hom
        (x ⊗ₜ[(situation g d hvan).affineBaseRing] m))
    exact happ.trans (hres₁.trans (hres₂.trans hsm))

end Main

section Statement

open Stacks.AlgebraicGeometry.TopDegreeBaseChange

/-- **The last paragraph of the proof of [Stacks, Tag 0EX4].** Let `g : X₀ ⟶ Y₀` be proper onto
an affine locally Noetherian base with higher direct images vanishing above `d`, let `F₀` be
coherent, and let `u : Y ⟶ Y₀` be any morphism from an affine scheme. Then for the base change
`X = X₀ ×_{Y₀} Y` and `F = h^* F₀`, the module `H ᵈ (X, F)` is a finite `Γ(Y, ⊤)`-module. -/
theorem moduleFinite_cohomology_of_isPullback
    {X₀ Y₀ X Y : Scheme.{u}} (g : X₀ ⟶ Y₀) [IsProper g] [IsAffine Y₀]
    [IsLocallyNoetherian Y₀] (d : ℕ)
    (hvan : ∀ i : ℤ, (d : ℤ) < i → ∀ G : X₀.Modules, G.IsQuasicoherent →
      IsZero (((Scheme.Modules.pushforward g).rightDerivedPlus i).obj G))
    (F₀ : X₀.Modules) [_root_.SheafOfModules.IsCoherent F₀]
    [IsAffine Y] (h : X ⟶ X₀) (f : X ⟶ Y) (u : Y ⟶ Y₀) (sq : IsPullback h f g u)
    (F : X.Modules) (e : F ≅ (Scheme.Modules.pullback h).obj F₀) :
    Module.Finite Γ(Y, ⊤) ((ModuleCat.restrictScalars f.appTop.hom).obj
      (((moduleGlobalSections X).rightDerived d).obj F)) :=
  moduleFinite_cohomology_of_isPullback_of_isQuasicoherent g d hvan F₀
    (_root_.isQuasicoherent_of_isCoherent F₀) h f u sq F e

end Statement

end

end Stacks.AlgebraicGeometry.TopDegreeFiniteType

end
