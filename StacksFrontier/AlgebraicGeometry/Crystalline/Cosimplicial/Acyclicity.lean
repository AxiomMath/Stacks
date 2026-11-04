module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.Grp.Ulift
public import StacksFrontier.AlgebraicGeometry.Crystalline.Cosimplicial

/-!
# From a null homotopy of a cosimplicial module to the acyclicity of its Moore complex

A cosimplicial module `M_*` over a cosimplicial commutative ring `A_*` is carried here, by
`Crystalline.cosimplicialModuleForget`, to the cosimplicial abelian group of its underlying
additive groups, and from there by `AlgebraicTopology.alternatingCofaceMapComplex` to the Moore
cochain complex `M_0 → M_1 → M_2 → ⋯` of [Stacks, Tag 019I].  This file proves that a null
homotopy of `M_*` in the sense of [Stacks, Tag 07KB] — `Crystalline.Homotopic (𝟙 M_*) 0` — makes
that complex acyclic in every degree, and does the same after an arbitrary universe lift of the
coefficients.

That is the step which consumes [Stacks, Tag 07LA] in the proof of [Stacks, Tag 07LF]: the tag
delivers `Crystalline.Homotopic (𝟙 _) 0` for the cosimplicial module
`M_* ⊗̂_{D(*)} Ω^i_{D(*)}`, and what the proof needs is the vanishing of the homology of its
Moore complex.

## What is and is not proved

Proved, with no hypothesis beyond the null homotopy: the homology of the Moore complex of the
underlying cosimplicial abelian group vanishes in every degree, and so does the homology of the
Moore complex of any universe lift of it.  Nothing here is about the crystalline site, and
nothing identifies a cosimplicial group of sections with the underlying group of a cosimplicial
module; that identification is item 6 of the list of open steps in
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/AffineCohomology.lean` and is not touched.

This file also settles a question recorded in the module documentation of
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/TensorSheafVanishing.lean`, which said that
a bridge from `Crystalline.Homotopic (𝟙 _) 0` to the acyclicity of
`AlgebraicTopology.alternatingCofaceMapComplex` is unwritten because
`AlgebraicTopology.homotopic_alternatingCofaceMapComplex_map` "asks for the homotopy in the
shape of a map out of `Δ[1]` on a `CategoryTheory.CosimplicialObject`, and
`Crystalline.Homotopy` is in the presheaf-of-modules presentation".  **The first half of that is
not so**: that theorem asks for the family form of [Stacks, Tag 0FKJ], a map
`Δ[1]_n → (U_n ⟶ V_n)` for each `n`, which needs no products and is the same shape as the
`app` field of `Crystalline.Homotopy`.  The presentations do differ — the components of a
`Crystalline.Homotopy` are morphisms of `ModuleCat A_n` and its naturality square is stated
through `ModuleCat.restrictScalars` — but forgetting the module structure is the identity on
underlying functions, so the transfer is
`Crystalline.exists_homotopy_cosimplicialModuleForget_of_homotopy` below and uses no lemma
beyond `ConcreteCategory.congr_hom`.

## Main definitions

* `Crystalline.cosimplicialModuleForget` — the underlying cosimplicial abelian group of a
  cosimplicial module, as a functor.
* `Crystalline.cosimplicialModuleTransition` — the transition map of a cosimplicial module as an
  additive map between the degrees written `M(op (op n))`.
* `Crystalline.cosimplicialModuleForgetUliftIso` — an isomorphism onto the universe lift of
  `Crystalline.cosimplicialModuleForget` of a cosimplicial module, assembled from degreewise
  additive isomorphisms written at that spelling.

## Main results

* `Crystalline.exists_homotopy_cosimplicialModuleForget_of_homotopy` — a homotopy of
  cosimplicial modules gives a homotopy of the underlying cosimplicial abelian groups, in the
  family form of [Stacks, Tag 0FKJ].
* `Crystalline.homotopic_cosimplicialModuleForget_map` — hence homotopic morphisms of
  cosimplicial modules have homotopic underlying morphisms.
* `Crystalline.isZero_homology_alternatingCofaceMapComplex_of_homotopic_id_zero` — **the
  acyclicity**: if `𝟙 M_*` is homotopic to `0` then the Moore complex of the underlying
  cosimplicial abelian group has vanishing homology in every degree.
* `Crystalline.isZero_homology_alternatingCofaceMapComplex_uliftFunctor_of_homotopic_id_zero` —
  the same after lifting the coefficients to a larger universe.
* `Crystalline.isZero_homology_alternatingCofaceMapComplex_of_iso` — that acyclicity transports
  across an isomorphism of cosimplicial objects.

## Implementation notes

**The reindexing along `CategoryTheory.opOp` is undone here, with the cosimplicial module a
variable, and it cannot be undone at a concrete one.**  `Crystalline.cosimplicialModuleForget` is
`CategoryTheory.PresheafOfModules.toPresheaf` whiskered with `CategoryTheory.opOp`, so the degree
`n` of its value is indexed by `(opOp SimplexCategory).obj n`, whereas every degreewise
construction over a concrete cosimplicial module — a tensor product, an exterior power — is
written at `op (op n)`.  The index terms are definitionally equal and `whnf` identifies them in
one step, but when they occur as the argument of `M.obj` for a concrete `M` the unifier does not
reach that step: it attempts congruence first, fails, and unfolds `M.obj` on both sides instead.
For `M = L_* ⊗ ⋀ⁱ Ω_{D(*)}` it then descends through the tensor product into the exterior-algebra
tower carrying two differently-spelled index and instance terms, and does not terminate inside
the heartbeat budget.  With `M` a variable, each of the three statements below is
immediate; the bare index substitution `M.obj ((opOp _).obj n) = M.obj (op (op n))` is immediate
at `L_* ⊗ L_*`, at `L_* ⊗ Ω_{D(*)}` and at `⋀ⁱ Ω_{D(*)}` on its own, and exhausts the budget at
`L_* ⊗ ⋀ⁱ Ω_{D(*)}` — it is the exterior power *under* the tensor product, and neither factor
alone.

`Crystalline.cosimplicialModuleTransition` and `Crystalline.cosimplicialModuleForgetUliftIso`
are therefore stated with `M` a variable and consumed by instantiation, where no unification of
the two index spellings is asked for at all.  **No heartbeat limit is raised anywhere**, here or
at the use site.

## References

* [Stacks Project, Tag 019I](https://stacks.math.columbia.edu/tag/019I)
* [Stacks Project, Tag 07KB](https://stacks.math.columbia.edu/tag/07KB)
* [Stacks Project, Tag 0FKJ](https://stacks.math.columbia.edu/tag/0FKJ)
* [Stacks Project, Tag 01A0](https://stacks.math.columbia.edu/tag/01A0)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology Opposite Simplicial

universe v u

namespace Crystalline

variable {A : CosimplicialObject CommRingCat.{u}}

/-- **The underlying cosimplicial abelian group of a cosimplicial module.**  A
`Crystalline.CosimplicialModule A` is a presheaf of modules on `SimplexCategoryᵒᵖ`; forgetting
the module structure and reindexing along `CategoryTheory.opOp` turns it into a functor out of
the simplex category, which is what `AlgebraicTopology.alternatingCofaceMapComplex` consumes. -/
noncomputable def cosimplicialModuleForget (A : CosimplicialObject CommRingCat.{u}) :
    CosimplicialModule A ⥤ CosimplicialObject AddCommGrpCat.{u} :=
  PresheafOfModules.toPresheaf _ ⋙
    (Functor.whiskeringLeft SimplexCategory (SimplexCategoryᵒᵖ)ᵒᵖ AddCommGrpCat.{u}).obj
      (opOp SimplexCategory)

/-! ### The degrees and the transition maps at the `op (op n)` spelling of the index -/

/-- **The transition map of a cosimplicial module along `φ : ⦋n⦌ ⟶ ⦋m⦌`, as an additive map
between the degrees written `M(op (op n))` and `M(op (op m))`.**

`Crystalline.cosimplicialModuleForget` reindexes along `CategoryTheory.opOp`, so the degree `n`
of the cosimplicial abelian group it produces is indexed by `(opOp SimplexCategory).obj n` while
every other description of a degree of a cosimplicial module is indexed by `op (op n)`.  The two
index terms are definitionally equal, but see the implementation notes: the substitution must be
performed here, with `M` a *variable*, and not at a concrete `M`. -/
noncomputable def cosimplicialModuleTransition (M : CosimplicialModule A)
    {n m : SimplexCategory} (φ : n ⟶ m) :
    (M.obj (op (op n)) : Type u) →+ (M.obj (op (op m)) : Type u) :=
  (M.map φ.op.op).hom.toAddMonoidHom

/-- **The degree `n` of the underlying cosimplicial abelian group of `M_*` is `M(op (op n))`.** -/
theorem cosimplicialModuleForget_obj_obj (M : CosimplicialModule A) (n : SimplexCategory) :
    (((cosimplicialModuleForget A).obj M).obj n : Type u) = (M.obj (op (op n)) : Type u) :=
  rfl

/-- **The transition map of the underlying cosimplicial abelian group of `M_*` is
`Crystalline.cosimplicialModuleTransition`.** -/
theorem cosimplicialModuleForget_map_apply (M : CosimplicialModule A) {n m : SimplexCategory}
    (φ : n ⟶ m) (x : (((cosimplicialModuleForget A).obj M).obj n : Type u)) :
    ((cosimplicialModuleForget A).obj M).map φ x = cosimplicialModuleTransition M φ x :=
  rfl

/-- **An isomorphism of cosimplicial abelian groups onto the universe lift of the underlying
cosimplicial abelian group of a cosimplicial module, from degreewise additive isomorphisms
written at the `op (op n)` spelling of the index.**

This is the assembly step `CategoryTheory.NatIso.ofComponents` performs, with the reindexing
along `CategoryTheory.opOp` and the universe lift both absorbed here: the components and the
naturality condition it asks for are stated at `M.obj (op (op n))` and about
`Crystalline.cosimplicialModuleTransition`, which is the spelling a degreewise construction over
a concrete `M` is available in.  See the implementation notes. -/
noncomputable def cosimplicialModuleForgetUliftIso (M : CosimplicialModule A)
    (K : CosimplicialObject AddCommGrpCat.{max u v})
    (comp : ∀ n : SimplexCategory,
      (K.obj n : Type max u v) ≃+ ULift.{v, u} (M.obj (op (op n)) : Type u))
    (hcomp : ∀ {n m : SimplexCategory} (φ : n ⟶ m) (x : (K.obj n : Type max u v)),
      (comp m (K.map φ x)).down = cosimplicialModuleTransition M φ (comp n x).down) :
    K ≅ (cosimplicialModuleForget A).obj M ⋙ AddCommGrpCat.uliftFunctor.{v, u} :=
  NatIso.ofComponents (fun n ↦ AddEquiv.toAddCommGrpIso (comp n)) fun {n m} φ ↦ by
    ext x
    exact congrArg ULift.up (hcomp φ x)

/-- **The Moore cochain complex of [Stacks, Tag 019I] carries the zero morphism to zero.**  Its
component in degree `n` is the component of the morphism at `⦋n⦌`. -/
theorem alternatingCofaceMapComplex_map_zero {C : Type*} [Category C] [Preadditive C]
    (U V : CosimplicialObject C) :
    (alternatingCofaceMapComplex C).map (0 : U ⟶ V) = 0 := by
  ext n
  rfl

/-- The naturality square of a homotopy of cosimplicial modules, read on an element: the
restriction of scalars that `Crystalline.Homotopy` states it through does not change the
underlying function. -/
private theorem homotopy_app_naturality_apply {K M : CosimplicialModule A} {a b : K ⟶ M}
    (h : Homotopy a b) {n m : SimplexCategory} (f : n ⟶ m)
    (α : (Δ[1] : SSet.{0}).obj (op m)) (x : K.obj (op (op n))) :
    h.app m α (K.map f.op.op x) =
      M.map f.op.op (h.app n ((Δ[1] : SSet.{0}).map f.op α) x) := by
  have hx := ConcreteCategory.congr_hom (h.naturality f α) x
  simp only [ConcreteCategory.comp_apply, ModuleCat.restrictScalars.map_apply] at hx
  exact hx

/-- **The homology of the Moore cochain complex is invariant under isomorphism of cosimplicial
objects.**  The Moore complex of [Stacks, Tag 019I] is a functor, so an isomorphism of
cosimplicial objects induces an isomorphism of cochain complexes and hence of their homology. -/
theorem isZero_homology_alternatingCofaceMapComplex_of_iso {C : Type*} [Category C]
    [Preadditive C] [CategoryWithHomology C] {U V : CosimplicialObject C} (e : U ≅ V) (j : ℕ)
    (h : IsZero (((alternatingCofaceMapComplex C).obj V).homology j)) :
    IsZero (((alternatingCofaceMapComplex C).obj U).homology j) :=
  h.of_iso ((HomologicalComplex.homologyFunctor C (ComplexShape.up ℕ) j).mapIso
    ((alternatingCofaceMapComplex C).mapIso e))

/-- **A homotopy of cosimplicial modules is a homotopy of the underlying cosimplicial abelian
groups.**  The components are the same linear maps, read as additive maps, and the naturality
square is the naturality square of `Crystalline.Homotopy` with the restriction of scalars
forgotten; the two agree on underlying functions.

The conclusion is spelled as the family of [Stacks, Tag 0FKJ] verbatim, which is the hypothesis
of `AlgebraicTopology.homotopic_alternatingCofaceMapComplex_map`. -/
theorem exists_homotopy_cosimplicialModuleForget_of_homotopy {K M : CosimplicialModule A}
    {a b : K ⟶ M} (h : Homotopy a b) :
    ∃ H : ∀ n : SimplexCategory, (Δ[1] : SSet.{0}).obj (op n) →
        (((cosimplicialModuleForget A).obj K).obj n ⟶
          ((cosimplicialModuleForget A).obj M).obj n),
      (∀ ⦃n m : SimplexCategory⦄ (f : n ⟶ m) (α : (Δ[1] : SSet.{0}).obj (op m)),
          ((cosimplicialModuleForget A).obj K).map f ≫ H m α =
            H n ((Δ[1] : SSet.{0}).map f.op α) ≫ ((cosimplicialModuleForget A).obj M).map f) ∧
        (∀ n : SimplexCategory, H n (SSet.stdSimplex.const 1 0 (op n)) =
            ((cosimplicialModuleForget A).map a).app n) ∧
          (∀ n : SimplexCategory, H n (SSet.stdSimplex.const 1 1 (op n)) =
            ((cosimplicialModuleForget A).map b).app n) := by
  refine ⟨fun n α ↦ AddCommGrpCat.ofHom (h.app n α).hom.toAddMonoidHom, ?_, ?_, ?_⟩
  · intro n m f α
    ext x
    exact homotopy_app_naturality_apply h f α x
  · intro n
    ext x
    exact ConcreteCategory.congr_hom (h.app_zero n) x
  · intro n
    ext x
    exact ConcreteCategory.congr_hom (h.app_one n) x

/-- **Homotopic morphisms of cosimplicial modules have homotopic underlying morphisms of
cosimplicial abelian groups.**  Both relations are the equivalence relation generated by the
existence of a homotopy, so this is
`Crystalline.exists_homotopy_cosimplicialModuleForget_of_homotopy` propagated along
`Relation.EqvGen.map`. -/
theorem homotopic_cosimplicialModuleForget_map {K M : CosimplicialModule A} {a b : K ⟶ M}
    (h : Homotopic a b) :
    Relation.EqvGen
      (fun x y : (cosimplicialModuleForget A).obj K ⟶ (cosimplicialModuleForget A).obj M ↦
        ∃ H : ∀ n : SimplexCategory, (Δ[1] : SSet.{0}).obj (op n) →
            (((cosimplicialModuleForget A).obj K).obj n ⟶
              ((cosimplicialModuleForget A).obj M).obj n),
          (∀ ⦃n m : SimplexCategory⦄ (f : n ⟶ m) (α : (Δ[1] : SSet.{0}).obj (op m)),
              ((cosimplicialModuleForget A).obj K).map f ≫ H m α =
                H n ((Δ[1] : SSet.{0}).map f.op α) ≫
                  ((cosimplicialModuleForget A).obj M).map f) ∧
            (∀ n : SimplexCategory, H n (SSet.stdSimplex.const 1 0 (op n)) = x.app n) ∧
              (∀ n : SimplexCategory, H n (SSet.stdSimplex.const 1 1 (op n)) = y.app n))
      ((cosimplicialModuleForget A).map a) ((cosimplicialModuleForget A).map b) :=
  Relation.EqvGen.map _
    (fun _ _ hab ↦ exists_homotopy_cosimplicialModuleForget_of_homotopy hab.some) h

/-- The underlying morphism of the zero morphism of cosimplicial modules is zero. -/
@[simp]
theorem cosimplicialModuleForget_map_zero (K M : CosimplicialModule A) :
    (cosimplicialModuleForget A).map (0 : K ⟶ M) = 0 := by
  ext n x
  rfl

/-- The Moore complex of a cosimplicial object has zero homology when the identity is homotopic to
zero. -/
private theorem isZero_homology_of_homotopic_id_zero {C : Type*} [Category C] [Preadditive C]
    [CategoryWithHomology C] {U : CosimplicialObject C}
    (h : homotopic C (ComplexShape.up ℕ) ((alternatingCofaceMapComplex C).map (𝟙 U))
      ((alternatingCofaceMapComplex C).map 0)) (j : ℕ) :
    IsZero (((alternatingCofaceMapComplex C).obj U).homology j) := by
  obtain ⟨ho⟩ := h
  have hid := ho.homologyMap_eq j
  rw [(alternatingCofaceMapComplex C).map_id, alternatingCofaceMapComplex_map_zero,
    HomologicalComplex.homologyMap_id, HomologicalComplex.homologyMap_zero] at hid
  exact (IsZero.iff_id_eq_zero _).2 hid

/-- **The acyclicity consumed by [Stacks, Tag 07LF].**  If the identity of a cosimplicial module
`M_*` over a cosimplicial commutative ring is homotopic to zero in the sense of
[Stacks, Tag 07KB], then the Moore cochain complex `M_0 → M_1 → M_2 → ⋯` of [Stacks, Tag 019I]
built from the underlying cosimplicial abelian group has vanishing homology in every degree.

`AlgebraicTopology.homotopic_alternatingCofaceMapComplex_map` ([Stacks, Tag 01A0]) turns the
null homotopy into a chain homotopy from the identity of the complex to its zero endomorphism,
and a complex whose identity is null homotopic has zero homology by
`Homotopy.homologyMap_eq`. -/
theorem isZero_homology_alternatingCofaceMapComplex_of_homotopic_id_zero
    {M : CosimplicialModule A} (h : Homotopic (𝟙 M) 0) (j : ℕ) :
    IsZero (((alternatingCofaceMapComplex AddCommGrpCat.{u}).obj
      ((cosimplicialModuleForget A).obj M)).homology j) := by
  have hrel := homotopic_cosimplicialModuleForget_map h
  rw [(cosimplicialModuleForget A).map_id, cosimplicialModuleForget_map_zero] at hrel
  exact isZero_homology_of_homotopic_id_zero (homotopic_alternatingCofaceMapComplex_map hrel) j

/-- **The acyclicity after a universe lift.**  The Moore complex of the universe lift of the
underlying cosimplicial abelian group of a null homotopic cosimplicial module has vanishing
homology in every degree.

The crystalline cohomology of `Cris(X/S)` has its coefficients one universe above the modules of
a sheaf of `𝒪_{X/S}`-modules, for the reason recorded in
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/Cohomology.lean`, so this and not the
preceding statement is the form [Stacks, Tag 07LF] consumes.  Universe lifting is an additive
functor, so it carries the homotopy of
`Crystalline.exists_homotopy_cosimplicialModuleForget_of_homotopy` to a homotopy by clause (2)
of [Stacks, Tag 019Y], `CategoryTheory.homotopic_whiskerRight`. -/
theorem isZero_homology_alternatingCofaceMapComplex_uliftFunctor_of_homotopic_id_zero
    {M : CosimplicialModule A} (h : Homotopic (𝟙 M) 0) (j : ℕ) :
    IsZero (((alternatingCofaceMapComplex AddCommGrpCat.{max u v}).obj
      ((cosimplicialModuleForget A).obj M ⋙
        AddCommGrpCat.uliftFunctor.{v, u})).homology j) := by
  have hrel := homotopic_whiskerRight.2.1 AddCommGrpCat.uliftFunctor.{v, u}
    (homotopic_cosimplicialModuleForget_map h)
  rw [(cosimplicialModuleForget A).map_id, cosimplicialModuleForget_map_zero] at hrel
  have hzero : Functor.whiskerRight (0 :
      (cosimplicialModuleForget A).obj M ⟶ (cosimplicialModuleForget A).obj M)
      AddCommGrpCat.uliftFunctor.{v, u} = 0 := by
    ext n x
    rfl
  have hone : Functor.whiskerRight (𝟙 ((cosimplicialModuleForget A).obj M))
      AddCommGrpCat.uliftFunctor.{v, u} = 𝟙 _ := by
    ext n x
    rfl
  rw [hzero, hone] at hrel
  exact isZero_homology_of_homotopic_id_zero (homotopic_alternatingCofaceMapComplex_map hrel) j

end Crystalline

end
