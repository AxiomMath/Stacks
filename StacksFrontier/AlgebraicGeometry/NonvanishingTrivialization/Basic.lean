module

public import StacksFrontier.AlgebraicGeometry.InvertibleTrivialization.Sheaf

/-!
# A section trivializes an invertible module on its nonvanishing locus

Let `(X, 𝒪_X)` be a ringed space all of whose stalks `𝒪_{X,x}` are local rings, let `L` be an
invertible sheaf of `𝒪_X`-modules and let `s ∈ Γ(X, L)` be a global section. Multiplication by
`s` is a morphism `𝒪_X ⟶ L` of sheaves of modules, and this file proves that its restriction to
the nonvanishing locus `X_s` of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/FinitePresentationStalk.lean` is an isomorphism.
This is the *trivialization* assertion of
[Stacks, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY), the openness assertion being the
already available `Stacks.SheafOfModules.isOpen_nonvanishingLocus`.

Also recorded here is quasi-coherence of an invertible module, in instance form. Mathlib has no
such instance: it makes `SheafOfModules.IsQuasicoherent` an instance for a *locally free* sheaf
of modules, and local freeness of an invertible module is itself a theorem —
`Stacks.SheafOfModules.isFiniteLocallyFreeOfRank_one_of_isInvertible`, which is clause 2 of
[Stacks, Tag 0B8M](https://stacks.math.columbia.edu/tag/0B8M). The two results belong together
because they rest on the same trivialization of `L` by a nonvanishing section.

## Main results

* `Stacks.SheafOfModules.isIso_of_isIso_val_app`: a morphism of sheaves of modules all of whose
  components are isomorphisms is an isomorphism.
* `Stacks.SheafOfModules.bijective_smul_eval_of_le_nonvanishingOpen`: for every open `V ⊆ X_s`
  the map `c ↦ c • s|_V` is a bijection `𝒪_X(V) → L(V)`.
* `Stacks.SheafOfModules.isIso_over_nonvanishingOpen`: **Tag 01CY**, trivialization clause. The
  morphism `𝒪_X ⟶ L` given by `s` becomes an isomorphism over `X_s`.
  `Stacks.SheafOfModules.Scheme.isIso_over_nonvanishingOpen` is the same for a scheme, where
  the stalks of the structure sheaf are local rings automatically.
* `Stacks.SheafOfModules.isQuasicoherent_of_isInvertible` and
  `Stacks.SheafOfModules.Scheme.isQuasicoherent_of_isInvertible`: an invertible sheaf of modules
  is quasi-coherent, in instance form.
* `Stacks.SheafOfModules.grpGerm_eval` and `Stacks.SheafOfModules.grpGerm_res`: the germ of a
  global section does not depend on the open it is read over, and the germ of a restriction is
  the germ.
* `Stacks.SheafOfModules.bijective_stalkMapL_unitHomEquiv_symm` and
  `Stacks.SheafOfModules.stalkMapL_unitHomEquiv_symm_comp`: the stalk-level statement and the
  computation of the stalk map of multiplication by a global section.

## Implementation notes

The whole content is the bijectivity statement
`bijective_smul_eval_of_le_nonvanishingOpen`, and it is proved on stalks. The point of the
nonvanishing locus is exactly that the germ of `s` at each of its points escapes `𝔪_x L_x`, and
over a local ring an element of an invertible module that escapes `𝔪 M` is a basis: that is the
algebraic core
`Stacks.SheafOfModules.Invertible.bijective_smul_of_notMem_maximalIdeal_smul_top`, which is not
re-derived here. The stalk `L_x` is an invertible `𝒪_{X,x}`-module through
`Stacks.SheafOfModules.stalkPairing`, so no finiteness input is needed.

Passing from the stalks back to sections is Mathlib's
`TopCat.Presheaf.app_bijective_of_stalkFunctor_map_bijective`: a morphism of sheaves of abelian
groups which is bijective on the stalks over an open `V` is bijective on the sections over `V`.
Surjectivity is the half that needs the sheaf condition, and this is why no trivializing *pair*
of sections has to be produced on `X_s` — the local pairs of
`Stacks.SheafOfModules.exists_tensorPairing_eq_unitSection` only cover a neighbourhood of each
point, while `X_s` is their union.

Two identifications are used and both hold by `rfl`, so they are made silently: the component of
`L.unitHomEquiv.symm s` at `V` is `c ↦ c • s|_V`, because `PresheafOfModules.unitHomEquiv` is
built from `LinearMap.ringLmapEquivSelf`; and the stalk map of the induced morphism of sheaves of
abelian groups is `Stacks.SheafOfModules.TensorStalkRingedSpace.stalkMapL`, because both are
`TopCat.Presheaf.stalkFunctor` applied to the underlying presheaf morphism.

The `IsIso` statement is about the restriction functor `SheafOfModules.Hom.over` to the localized
site `Over X_s`, which is the shape Tag 01CY is consumed in. Its source
`(SheafOfModules.unit 𝒪_X).over X_s` is `SheafOfModules.unit (𝒪_X.over X_s)` by definition.

**Which `IsInvertible`.** `Stacks.SheafOfModules.IsInvertible` of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/TensorInvertible.lean`, the class that
`Stacks.SheafOfModules.nonvanishingOpen`, `stalkPairing` and
`isFiniteLocallyFreeOfRank_one_of_isInvertible` all key on. It is *not*
`AlgebraicGeometry.SheafOfModules.IsInvertible` of
`StacksFrontier/Topology/Sheaves/Modules/Invertible.lean`; the two classes have byte-identical
definitions but are distinct constants, and no bridge between them is written here.

## References

* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
* [Stacks Project, Tag 0B8K](https://stacks.math.columbia.edu/tag/0B8K)
* [Stacks Project, Tag 0B8M](https://stacks.math.columbia.edu/tag/0B8M)
* [Stacks Project, Tag 01BD](https://stacks.math.columbia.edu/tag/01BD)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry IsLocalRing
open Stacks.SheafOfModules.TensorStalkRingedSpace

universe u v₁ u₁

namespace Stacks.SheafOfModules

section Componentwise

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  {M N : SheafOfModules.{u} R}

/-- A morphism of sheaves of modules whose component at every object of the site is an
isomorphism is an isomorphism. The inverse is assembled by `PresheafOfModules.isoMk`, whose
naturality square is the one the morphism already satisfies, and
`SheafOfModules.forget` reflects isomorphisms. -/
theorem isIso_of_isIso_val_app (φ : M ⟶ N) (h : ∀ A, IsIso (φ.val.app A)) : IsIso φ := by
  let e : (SheafOfModules.forget R).obj M ≅ (SheafOfModules.forget R).obj N :=
    PresheafOfModules.isoMk (fun A => @asIso _ _ _ _ (φ.val.app A) (h A))
      (fun A B f => φ.val.naturality f)
  have he : (SheafOfModules.forget R).map φ = e.hom := by
    apply PresheafOfModules.hom_ext
    intro A
    rfl
  have : IsIso ((SheafOfModules.forget R).map φ) := by rw [he]; infer_instance
  exact isIso_of_reflects_iso φ (SheafOfModules.forget R)

end Componentwise

variable {X : RingedSpace.{u, u}} {L N : SheafOfModules.{u} (structureSheafRing X)}

/-- The germ of a global section does not depend on the open it is restricted to. -/
theorem grpGerm_eval (s : L.sections) (y : X.carrier) (V : Opens X.carrier) (hyV : y ∈ V) :
    grpGerm X L.val y V hyV (s.eval (op V))
      = grpGerm X L.val y ⊤ (Opens.mem_top y) (s.eval (op ⊤)) := by
  have hres : L.val.map (homOfLE (le_top (a := V))).op (s.eval (op ⊤)) = s.eval (op V) :=
    PresheafOfModules.sections_property s (homOfLE (le_top (a := V))).op
  rw [← hres]
  exact TopCat.Presheaf.germ_res_apply (C := AddCommGrpCat.{u}) L.val.presheaf
    (homOfLE (le_top (a := V))) y hyV (s.eval (op ⊤))

/-- **The germ of a restriction is the germ.**  Restricting a section from `U` to a smaller
open `V` containing `x` does not change its germ at `x`.

This is `TopCat.Presheaf.germ_res_apply` at the
  `Stacks.SheafOfModules.TensorStalkRingedSpace.grpGerm` spelling; the two
differ by the coercion through which the germ is applied (`AddMonoidHom` against
`ConcreteCategory.hom`), which is enough to stop a `rw`.  A private copy of this statement
sits at `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/IdealTorsionFree.lean`; deduplicating the two needs the
lemma to live in `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/TensorStalkRingedSpace.lean`, where
`grpGerm` is defined and which this file does not precede. -/
theorem grpGerm_res (U V : Opens X.carrier) (hVU : V ≤ U) (y : X.carrier) (hyV : y ∈ V)
    (a : L.val.obj (op U)) :
    grpGerm X L.val y V hyV (ConcreteCategory.hom (L.val.map (homOfLE hVU).op) a) =
      grpGerm X L.val y U (hVU hyV) a := by
  show (TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) L.val.presheaf V y hyV).hom
      (ConcreteCategory.hom (L.val.presheaf.map (homOfLE hVU).op)
        ((PresheafOfModules.presheaf_obj_coe (M := L.val) (op U)).symm ▸ a)) = _
  rw [TopCat.Presheaf.germ_res_apply (C := AddCommGrpCat.{u}) L.val.presheaf
    (homOfLE hVU) y hyV _]
  rfl

/-- The stalk map of multiplication by a global section `s`, evaluated on the germ of a section
`α` of the structure sheaf: it is `germ α` times the germ of `s`. -/
theorem stalkMapL_unitHomEquiv_symm_grpGerm (s : L.sections) (y : X.carrier)
    (W : Opens X.carrier) (hyW : y ∈ W) (α : X.presheaf.obj (op W)) :
    stalkMapL X (SheafOfModules.unit (structureSheafRing X)).val L.val
        (L.unitHomEquiv.symm s).val y
        (grpGerm X (SheafOfModules.unit (structureSheafRing X)).val y W hyW α)
      = ringGerm X y W hyW α • grpGerm X L.val y ⊤ (Opens.mem_top y) (s.eval (op ⊤)) :=
  have happ : ((L.unitHomEquiv.symm s).val.app (op W)).hom α = α • s.eval (op W) := rfl
  (stalkMapL_germ X (L.unitHomEquiv.symm s).val y W hyW α).trans <|
    (congrArg (grpGerm X L.val y W hyW) happ).trans <|
      (stalkModule_germ_smul X L.val y W hyW α (s.eval (op W))).trans <|
        congrArg (fun m => ringGerm X y W hyW α • m) (grpGerm_eval s y W hyW)

/-- Read through the identification of `(𝒪_X)_y` with the stalk of the structure sheaf regarded
as a module over itself, the stalk map of multiplication by `s` is multiplication by the germ of
`s`. -/
theorem stalkMapL_unitHomEquiv_symm_comp (s : L.sections) (y : X.carrier) :
    (stalkMapL X (SheafOfModules.unit (structureSheafRing X)).val L.val
        (L.unitHomEquiv.symm s).val y) ∘ (unitStalkLinearEquiv X y)
      = fun c : ringStalk X y => c • grpGerm X L.val y ⊤ (Opens.mem_top y) (s.eval (op ⊤)) := by
  funext c
  obtain ⟨W, hyW, α, rfl⟩ := X.presheaf.exists_germ_eq c
  have hu : unitStalkLinearEquiv X y (ringGerm X y W hyW α)
      = grpGerm X (SheafOfModules.unit (structureSheafRing X)).val y W hyW α := by
    rw [← unitStalkLinearEquiv_symm_grpGerm X y W hyW α, LinearEquiv.apply_symm_apply]
  exact (congrArg (stalkMapL X (SheafOfModules.unit (structureSheafRing X)).val L.val
      (L.unitHomEquiv.symm s).val y) hu).trans
    (stalkMapL_unitHomEquiv_symm_grpGerm s y W hyW α)

variable [∀ x : X.carrier, IsLocalRing (ringStalk X x)]

/-- At a point of the nonvanishing locus, the stalk map of multiplication by `s` is bijective:
the germ of `s` escapes `𝔪_y L_y`, and `L_y` is an invertible `𝒪_{X,y}`-module, so the germ is a
basis by `Invertible.bijective_smul_of_notMem_maximalIdeal_smul_top`. -/
theorem bijective_stalkMapL_unitHomEquiv_symm
    (ψ : (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf, ((X)).IsSheaf⟩).obj (L)).obj
      (N)) ≅ SheafOfModules.unit (structureSheafRing X))
    (s : L.sections) (y : X.carrier) (hy : y ∈ nonvanishingLocus L s) :
    Function.Bijective (stalkMapL X (SheafOfModules.unit (structureSheafRing X)).val L.val
      (L.unitHomEquiv.symm s).val y) := by
  have hinv : Module.Invertible (ringStalk X y) (grpStalk X L.val y) := .left (stalkPairing ψ y)
  have hg : Function.Bijective
      (fun c : ringStalk X y => c • grpGerm X L.val y ⊤ (Opens.mem_top y) (s.eval (op ⊤))) :=
    Invertible.bijective_smul_of_notMem_maximalIdeal_smul_top _ hy
  refine (Function.Bijective.of_comp_iff _ (unitStalkLinearEquiv X y).bijective).mp ?_
  rw [stalkMapL_unitHomEquiv_symm_comp]
  exact hg

/-- **Multiplication by a global section is bijective on every open inside its nonvanishing
locus.** Bijectivity is checked on the stalks, where it is the algebraic core, and transported
to sections by `TopCat.Presheaf.app_bijective_of_stalkFunctor_map_bijective`. -/
theorem bijective_smul_eval_of_le_nonvanishingOpen
    (L : SheafOfModules.{u} (structureSheafRing X))
    [IsInvertible X.presheaf (structureSheafRing X).property L] (s : L.sections)
    (V : Opens X.carrier) (hV : V ≤ nonvanishingOpen L s) :
    Function.Bijective fun c : X.presheaf.obj (op V) => c • s.eval (op V) := by
  obtain ⟨N, ⟨ψ⟩⟩ := (isInvertible_iff_exists_tensor_iso_unit
    (O := X.presheaf) (hO := (structureSheafRing X).property) L).mp ‹_›
  exact TopCat.Presheaf.app_bijective_of_stalkFunctor_map_bijective
    ((SheafOfModules.toSheaf (structureSheafRing X)).map (L.unitHomEquiv.symm s)) V
    fun y hy => bijective_stalkMapL_unitHomEquiv_symm ψ s y (hV hy)

/-- **Stacks Project, Tag 01CY** (trivialization). For an invertible sheaf of modules `L` on a
ringed space all of whose stalks are local rings, and a global section `s` of `L`, the morphism
`𝒪_X ⟶ L` given by multiplication by `s` restricts to an isomorphism over the nonvanishing
locus `X_s`. -/
@[stacks 01CY "trivialization", instance]
theorem isIso_over_nonvanishingOpen (L : SheafOfModules.{u} (structureSheafRing X))
    [IsInvertible X.presheaf (structureSheafRing X).property L] (s : L.sections) :
    IsIso ((L.unitHomEquiv.symm s).over (nonvanishingOpen L s)) := by
  refine isIso_of_isIso_val_app _ fun A => ?_
  rw [ConcreteCategory.isIso_iff_bijective]
  exact bijective_smul_eval_of_le_nonvanishingOpen L s A.unop.left (leOfHom A.unop.hom)

/-- **An invertible sheaf of modules is quasi-coherent.** It is finite locally free of rank one
by `isFiniteLocallyFreeOfRank_one_of_isInvertible`, hence locally free, and a locally free sheaf
of modules is quasi-coherent (Tag 01C7). -/
instance (priority := 100) isQuasicoherent_of_isInvertible
    (L : SheafOfModules.{u} (structureSheafRing X))
    [IsInvertible X.presheaf (structureSheafRing X).property L] : L.IsQuasicoherent :=
  have := isFiniteLocallyFreeOfRank_one_of_isInvertible L
  have := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree L 1
  inferInstance

end Stacks.SheafOfModules

namespace Stacks.SheafOfModules

/-- **Stacks Project, Tag 01CY** (trivialization) for a scheme, where the stalks of the
structure sheaf are local rings automatically. -/
theorem Scheme.isIso_over_nonvanishingOpen (Y : Scheme.{u}) (L : Y.Modules)
    [IsInvertible Y.presheaf (structureSheafRing Y.toRingedSpace).property L] (s : L.sections) :
    IsIso ((L.unitHomEquiv.symm s).over (nonvanishingOpen (X := Y.toRingedSpace) L s)) :=
  have : ∀ z : Y.toRingedSpace.carrier, IsLocalRing (ringStalk Y.toRingedSpace z) :=
    fun z => Y.isLocalRing z
  _root_.Stacks.SheafOfModules.isIso_over_nonvanishingOpen (X := Y.toRingedSpace) L s

/-- **An invertible module on a scheme is quasi-coherent.** This is the form that the global
generation arguments of Chapter 31 consume. -/
instance (priority := 100) Scheme.isQuasicoherent_of_isInvertible (Y : Scheme.{u})
    (L : Y.Modules)
    [IsInvertible Y.presheaf (structureSheafRing Y.toRingedSpace).property L] :
    L.IsQuasicoherent :=
  have : ∀ z : Y.toRingedSpace.carrier, IsLocalRing (ringStalk Y.toRingedSpace z) :=
    fun z => Y.isLocalRing z
  _root_.Stacks.SheafOfModules.isQuasicoherent_of_isInvertible (X := Y.toRingedSpace) L

end Stacks.SheafOfModules

end
