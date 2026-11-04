module

public import StacksCore.CategoryTheory.Filtration.GradedStrict
public import StacksCore.CategoryTheory.Filtration.Subquotient
import StacksCore.Tactic.StacksAttribute

/-! # Homology of a complex of filtered objects: Stacks 0128

Stacks 0128: let `𝒜` be an abelian category and `A → B → C` a complex of filtered objects of `𝒜`
with `α : A → B` and `β : B → C` strict. Then `gr(Ker β / Im α) = Ker(gr β) / Im(gr α)`. Stacks'
proof: "formally from Stacks 05SP and `Coim α ≅ Im α`, `Coim β ≅ Im β` (Stacks 05SI)".

The setting is `S : ShortComplex (FilteredObject C I)` over an abelian category `C` and an
arbitrary index category `I`, so `α = S.f`, `β = S.g` and `S.zero : S.f ≫ S.g = 0`; the graded
pieces are taken along an arbitrary index arrow `φ : i ⟶ j` (`grMap φ`, the functor `F^j/F^i`),
Stacks' `gr^p` on `ℤᵒᵖ` being the case `φ = succHom p` (`gr p`).

* The exactness inputs: for a strict `f`, `gr_φ` preserves the kernel and the cokernel of `f`
  (the instances `preservesLimit_parallelPair_grMap_of_isStrict` and
  `preservesColimit_parallelPair_grMap_of_isStrict`). By Stacks 05SI the comparison
  `Coim f ⟶ Im f` is an isomorphism in `Fil(𝒜)`, so Stacks 0127 (4), (5) at one index arrow
  (`exact_grMap_kernel_ι_iff_mono`, `exact_grMap_cokernel_π_iff_epi`) give the exactness of
  `gr_φ(Ker f) → gr_φ(A) → gr_φ(B)` and `gr_φ(A) → gr_φ(B) → gr_φ(Coker f)`, whose outer maps
  are a monomorphism, resp. an epimorphism, by Stacks 05SP. On the explicit models `kernelObj f`
  and `cokernelObj f` of `StacksCore.CategoryTheory.Filtration.Limits` this reads
  `grMapKernelιIsKernel`, `grMapCokernelπIsCokernel`; Mathlib's `PreservesKernel.iso`,
  `KernelFork.mapIsLimit`, `IsIso (kernelComparison f (grMap φ))` and their duals follow. These
  four declarations live with Stacks 0127 in `StacksCore.CategoryTheory.Filtration.GradedStrict`.
* `Ker β / Im α` with the filtration of Stacks 0129: `kernelObjLift S : S.X₁ ⟶ kernelObj S.g` is
  the filtered lift of `α` through `Ker β` (with the induced filtration); its underlying morphism
  is `kernel.lift β.hom α.hom _` (`kernelObjLift_hom`), it is Mathlib's `kernel.lift S.g S.f _`
  in `Fil(𝒜)` transported along `kernelIsoKernelObj` (`kernel_lift_kernelIsoKernelObj_hom`), and
  it is strict when `α` is (`isStrict_kernelObjLift`, cancellation in Stacks 05SJ (2), `Ker β ⊆ B`
  being a strict monomorphism). Then `homologyObj S := cokernelObj (kernelObjLift S)` is
  `Ker β / Im α` with the quotient filtration of the induced filtration on `Ker β`, definitionally
  the subquotient `subquotientObj S.X₂ (kernel.lift β.hom α.hom _) (kernel.ι β.hom)` of Stacks 0129
  (`homologyObj_eq_subquotientObj`), so the two filtrations of 0129 agree on it with no
  hypothesis (`isStrictHom_subquotientHom`, `subquotientObj_subobject_eq_pullback`,
  `subquotientIsoPullbackObj` at `S.X₂ _ _`: the quotient filtration is the one induced from
  `B / Im α` along `Ker β / Im α ⟶ B / Im α`), with steps
  `F^i(Ker β / Im α) = π(Ker β ∩ F^iB)` (`homologyObj_subobject`); the projection
  `homologyπObj S : Ker β ⟶ Ker β / Im α` is a strict epimorphism.
* `Ker β / Im α` is the left homology of `S` computed in `Fil(𝒜)`: the models assemble into a
  left homology data `homologyObjLeftHomologyData S` for `S` (no hypothesis), whose `f'` is
  `kernelObjLift S` (`homologyObjLeftHomologyData_f'`) and whose cycles are
  `Ker β` (`cyclesIsoKernelObj : S.cycles ≅ kernelObj S.g`), giving
  `leftHomologyIsoHomologyObj : S.leftHomology ≅ homologyObj S`, compatible with the projections
  (`leftHomologyπ_comp_leftHomologyIsoHomologyObj_hom`,
  `homologyπObj_comp_leftHomologyIsoHomologyObj_inv`). This bridge follows the Limits.lean
  convention (Mathlib's object on the left, the model on the right); the tagged isomorphisms
  below are oriented as Stacks writes the equation, `gr(Ker β / Im α) ≅ …`.
* The tag: applied to `β` (strict) and to `kernelObjLift S` (strict because `α` is), `gr_φ`
  preserves the left homology data `homologyObjLeftHomologyData S`, hence the left homology of
  `S` (the instance `preservesLeftHomologyOf_grMap`; Mathlib's `LeftHomologyData.IsPreservedBy`
  and `Functor.PreservesLeftHomologyOf`, so `S.mapLeftHomologyIso (grMap φ)` is available).
  Mathlib's `LeftHomologyData.map` then makes `gr_φ(Ker β)`, `gr_φ(Ker β / Im α)`, `gr_φ` of the
  inclusion and `gr_φ` of the projection a left homology data for `gr_φ(S)`
  (`grMapLeftHomologyData`, whose `f'` is `gr_φ` of `A ⟶ Ker β`: `grMapLeftHomologyData_f'`),
  and `grMapHomologyIso : gr_φ(Ker β / Im α) ≅ (S.map (grMap φ)).homology` is Stacks 0128 along
  any index arrow, compatible with the homology class maps (through the cycles
  `grMapCyclesIsoKernelObj : cycles(gr_φ S) ≅ gr_φ(Ker β)`;
  (`grMap_map_homologyπObj_comp_grMapHomologyIso_hom`, `homologyπ_comp_grMapHomologyIso_inv`);
  `grMapHomologyIsoCokernelLift` is the literal `gr(Ker β / Im α) ≅ Coker(gr A ⟶ Ker(gr β))`.
  `grHomologyIso` is the form `gr^p(Ker β / Im α) ≅ H(gr^p S)` in Stacks' indexing and
  `grGradedHomologyIso` the form `gr(Ker β / Im α) ≅ H(gr S)` in `Gr(𝒜)`.

Strictness of `β` enters only through the kernel of `β`, strictness of `α` only through the
cokernel of `A ⟶ Ker β` (`isStrict_kernelObjLift`); `homologyObj`, `homologyObjLeftHomologyData`
and `leftHomologyIsoHomologyObj` need neither. Not done: naturality of `grMapHomologyIso` in
`S`; the dual model `Ker(Coker α → C)` (a right homology data) and its comparison with
`homologyObj`; `S.HasHomology` in `Fil(𝒜)` is not asserted (only `S.HasLeftHomology` is used
there, `Fil(𝒜)` not being abelian).
-/

@[expose] public section

namespace CategoryTheory

open Limits

variable {C : Type*} [Category* C] {I : Type*} [Category* I]

namespace FilteredObject

/-! ### `Ker β / Im α` with its filtration -/

section Homology

variable [Abelian C] (S : ShortComplex (FilteredObject C I))

/-- The filtered lift of `α = S.f : S.X₁ ⟶ S.X₂` through `Ker β ⊆ S.X₂` (with its induced
filtration); its underlying morphism is `kernel.lift β.hom α.hom _` (`kernelObjLift_hom`). -/
noncomputable def kernelObjLift : S.X₁ ⟶ kernelObj S.g :=
  (kernelIsLimit S.g).lift (KernelFork.ofι S.f S.zero)

/-- The underlying morphism of the filtered lift `A ⟶ Ker β` is Mathlib's `kernel.lift`. -/
@[simp] lemma kernelObjLift_hom :
    (kernelObjLift S).hom = kernel.lift S.g.hom S.f.hom (congrArg Hom.hom S.zero) := rfl

/-- `A ⟶ Ker β ⟶ B` is `α`. -/
@[reassoc (attr := simp)]
lemma kernelObjLift_comp_kernelι : kernelObjLift S ≫ kernelι S.g = S.f :=
  Fork.IsLimit.lift_ι (kernelIsLimit S.g)

/-- The filtered lift `A ⟶ Ker β` is Mathlib's lift into the kernel of `β` computed in `Fil(𝒜)`,
transported along `kernelIsoKernelObj`. -/
@[reassoc (attr := simp)]
lemma kernel_lift_kernelIsoKernelObj_hom :
    kernel.lift S.g S.f S.zero ≫ (kernelIsoKernelObj S.g).hom = kernelObjLift S :=
  (cancel_mono (kernelι S.g)).1 <| by
    rw [Category.assoc, kernelIsoKernelObj_hom_kernelι, kernel.lift_ι, kernelObjLift_comp_kernelι]

/-- Cancellation in Stacks 05SJ (2) (`isStrict_comp_iff_of_mono`): `α = (A ⟶ Ker β) ≫ (Ker β ⟶ B)`
with `Ker β ⟶ B` a strict monomorphism (`isStrict_pullbackHom`), so the filtered lift `A ⟶ Ker β`
is strict when `α` is. (An instance: the cancellation direction is a theorem, so type class search
has no route to `IsStrict (kernelObjLift S)`, and `preservesLeftHomologyOf_grMap` needs it.) -/
instance isStrict_kernelObjLift [IsStrict S.f] : IsStrict (kernelObjLift S) := by
  rw [← isStrict_comp_iff_of_mono (kernelObjLift S) (kernelι S.g), kernelObjLift_comp_kernelι]
  infer_instance

/-- Stacks' `Ker β / Im α` for the complex `α = S.f`, `β = S.g`: the cokernel of the filtered
lift `A ⟶ Ker β` computed in `Fil(𝒜)`, i.e. `Ker β / Im α` with the quotient filtration of the
induced filtration on `Ker β`, which is the subquotient of Stacks 0129
(`homologyObj_eq_subquotientObj`, steps `homologyObj_subobject`). Its underlying object is
Mathlib's `cokernel (kernel.lift β.hom α.hom _)`, by `rfl`. -/
noncomputable abbrev homologyObj : FilteredObject C I := cokernelObj (kernelObjLift S)

/-- `Ker β / Im α` is the subquotient of Stacks 0129 for `X := Im α ⊆ Y := Ker β ⊆ B`, so the
two filtrations of 0129 on it agree, with no hypothesis (`kernel.lift β.hom α.hom _` need not be
a monomorphism): the quotient filtration on `Ker β / Im α` is the one induced from `B / Im α`
along `Ker β / Im α ⟶ B / Im α` (`isStrictHom_subquotientHom S.X₂ _ _`; on the steps
`subquotientObj_subobject_eq_pullback S.X₂ _ _`, literally `subquotientIsoPullbackObj S.X₂ _ _`;
there `B / Im α` is `B / Im(kernel.lift β.hom α.hom _ ≫ kernel.ι β.hom)`, `kernel.lift_ι`). -/
theorem homologyObj_eq_subquotientObj :
    homologyObj S =
      subquotientObj S.X₂ (kernel.lift S.g.hom S.f.hom (congrArg Hom.hom S.zero))
        (kernel.ι S.g.hom) :=
  rfl

/-- The steps of `Ker β / Im α`: the images in `Ker β / Im α` of the steps `Ker β ∩ F^iB` of the
induced filtration on `Ker β` (Stacks 0129). -/
lemma homologyObj_subobject (i : I) :
    (homologyObj S).subobject i =
      (Subobject.exists (cokernel.π (kernel.lift S.g.hom S.f.hom (congrArg Hom.hom S.zero)))).obj
        ((Subobject.pullback (kernel.ι S.g.hom)).obj (S.X₂.subobject i)) :=
  subquotientObj_subobject S.X₂ _ _ i

/-- The projection `Ker β ⟶ Ker β / Im α`, a strict epimorphism: `IsStrict (homologyπObj S)`,
`Epi (homologyπObj S)` and `Epi (homologyπObj S).hom` are found by type class search through the
`abbrev`s (`isStrict_pushforwardHom` and the `cokernelπ` instances). Its underlying morphism is
`cokernel.π (kernel.lift β.hom α.hom _)`, by `rfl`. -/
noncomputable abbrev homologyπObj : kernelObj S.g ⟶ homologyObj S := cokernelπ (kernelObjLift S)

/-- The explicit models are a left homology data for `S` in `Fil(𝒜)`: `Ker β` with the induced
filtration is a kernel of `β` (`kernelIsLimit`), and `Ker β / Im α` is a cokernel of `A ⟶ Ker β`
(`cokernelIsColimit`). Its `f'` is `kernelObjLift S` (`homologyObjLeftHomologyData_f'`), which
is why `wπ` is `comp_cokernelπ`. No hypothesis. `implicit_reducible`, so that `simp` can unify
the implicit object `K` of Mathlib's `LeftHomologyData` API with `kernelObj S.g` and the `simps`
projections are usable by `dsimp`. -/
@[implicit_reducible, simps K H i π]
noncomputable def homologyObjLeftHomologyData : S.LeftHomologyData where
  K := kernelObj S.g
  H := homologyObj S
  i := kernelι S.g
  π := homologyπObj S
  wi := kernelι_comp S.g
  hi := kernelIsLimit S.g
  wπ := comp_cokernelπ (kernelObjLift S)
  hπ := cokernelIsColimit (kernelObjLift S)

/-- The lift `A ⟶ Ker β` of the left homology data of the explicit models is `kernelObjLift`. -/
@[simp] lemma homologyObjLeftHomologyData_f' :
    (homologyObjLeftHomologyData S).f' = kernelObjLift S :=
  rfl

/-- Mathlib's cycles of `S` in `Fil(𝒜)` are `Ker β` with the induced filtration; the iso is
`cyclesIso` of `homologyObjLeftHomologyData S`, typed on the model `kernelObj S.g` so that the
compatibility lemmas below are stated on one spelling of the object. -/
noncomputable def cyclesIsoKernelObj : S.cycles ≅ kernelObj S.g :=
  (homologyObjLeftHomologyData S).cyclesIso

/-- `S.cycles ≅ Ker β ⟶ B` is the inclusion of cycles. -/
@[reassoc (attr := simp)]
lemma cyclesIsoKernelObj_hom_comp_kernelι : (cyclesIsoKernelObj S).hom ≫ kernelι S.g = S.iCycles :=
  (homologyObjLeftHomologyData S).cyclesIso_hom_comp_i

/-- `Ker β ≅ S.cycles ⟶ B` is the inclusion `Ker β ⟶ B`. -/
@[reassoc (attr := simp)]
lemma cyclesIsoKernelObj_inv_comp_iCycles : (cyclesIsoKernelObj S).inv ≫ S.iCycles = kernelι S.g :=
  (homologyObjLeftHomologyData S).cyclesIso_inv_comp_iCycles

/-- Stacks' `Ker β / Im α` is the left homology of `S` computed in `Fil(𝒜)` (Mathlib's chosen
object on the left, the explicit model on the right, as `kernelIsoKernelObj`). -/
noncomputable def leftHomologyIsoHomologyObj : S.leftHomology ≅ homologyObj S :=
  (homologyObjLeftHomologyData S).leftHomologyIso

/-- `S.cycles ⟶ S.leftHomology ≅ Ker β / Im α` is `S.cycles ≅ Ker β ⟶ Ker β / Im α`. -/
@[reassoc (attr := simp)]
lemma leftHomologyπ_comp_leftHomologyIsoHomologyObj_hom :
    S.leftHomologyπ ≫ (leftHomologyIsoHomologyObj S).hom =
      (cyclesIsoKernelObj S).hom ≫ homologyπObj S :=
  (homologyObjLeftHomologyData S).leftHomologyπ_comp_leftHomologyIso_hom

/-- `Ker β ⟶ Ker β / Im α ≅ S.leftHomology` is `Ker β ≅ S.cycles ⟶ S.leftHomology`. -/
@[reassoc (attr := simp)]
lemma homologyπObj_comp_leftHomologyIsoHomologyObj_inv :
    homologyπObj S ≫ (leftHomologyIsoHomologyObj S).inv =
      (cyclesIsoKernelObj S).inv ≫ S.leftHomologyπ :=
  (homologyObjLeftHomologyData S).π_comp_leftHomologyIso_inv

end Homology

/-! ### Stacks 0128 -/

section Graded

variable [Abelian C] (S : ShortComplex (FilteredObject C I)) {i j : I} (φ : i ⟶ j)

/-- Stacks 0128, abstract form: for a complex `S` of strict morphisms, `gr_φ` preserves the left
homology of `S`, along any index arrow `φ`: it preserves the kernel of the strict `β`
(`preservesLimit_parallelPair_grMap_of_isStrict`) and the cokernel of `A ⟶ Ker β`, strict because
`α` is (`preservesColimit_parallelPair_grMap_of_isStrict`), i.e. the left homology data
`homologyObjLeftHomologyData S`. -/
@[stacks 0128 "`gr_φ` preserves the left homology of a complex of strict morphisms; any `φ`, `I`"]
instance preservesLeftHomologyOf_grMap [IsStrict S.f] [IsStrict S.g] :
    (grMap φ).PreservesLeftHomologyOf S :=
  have : (homologyObjLeftHomologyData S).IsPreservedBy (grMap φ) :=
    ⟨preservesLimit_parallelPair_grMap_of_isStrict S.g φ,
      preservesColimit_parallelPair_grMap_of_isStrict (kernelObjLift S) φ⟩
  Functor.PreservesLeftHomologyOf.mk' (grMap φ) (homologyObjLeftHomologyData S)

/-- Stacks 0128: `gr_φ(Ker β)`, `gr_φ(Ker β / Im α)`, with `gr_φ` of the kernel inclusion and of
the projection, form a left homology data for `gr_φ(S)` (`LeftHomologyData.map_K`, `map_H`,
`map_i`, `map_π`), along any index arrow `φ`; its `f'` is `gr_φ` of the lift `A ⟶ Ker β`
(`grMapLeftHomologyData_f'`). -/
noncomputable abbrev grMapLeftHomologyData [IsStrict S.f] [IsStrict S.g] :
    (S.map (grMap φ)).LeftHomologyData :=
  (homologyObjLeftHomologyData S).map (grMap φ)

/-- The lift of `gr_φ(α)` through the kernel `gr_φ(Ker β) ⟶ gr_φ(B)` of `gr_φ(β)` is `gr_φ` of the
filtered lift `A ⟶ Ker β`: `LeftHomologyData.map_f'` followed by `homologyObjLeftHomologyData_f'`
(`simp` rewrites the left-hand side with these two, so this is not a `simp` lemma). -/
lemma grMapLeftHomologyData_f' [IsStrict S.f] [IsStrict S.g] :
    (grMapLeftHomologyData S φ).f' = (grMap φ).map (kernelObjLift S) :=
  (ShortComplex.LeftHomologyData.map_f' _ _).trans
    (congrArg _ (homologyObjLeftHomologyData_f' S))

/-- The cycles of `gr_φ(S)` are `gr_φ(Ker β)`: `cyclesIso` of `grMapLeftHomologyData S φ`, typed on
`(grMap φ).obj (kernelObj S.g)` so that the compatibility lemmas below are stated on one spelling
of the object. -/
noncomputable def grMapCyclesIsoKernelObj [IsStrict S.f] [IsStrict S.g] :
    (S.map (grMap φ)).cycles ≅ (grMap φ).obj (kernelObj S.g) :=
  (grMapLeftHomologyData S φ).cyclesIso

/-- `cycles(gr_φ S) ≅ gr_φ(Ker β) ⟶ gr_φ(B)` is the inclusion of cycles. -/
@[reassoc (attr := simp)]
lemma grMapCyclesIsoKernelObj_hom_comp_map_kernelι [IsStrict S.f] [IsStrict S.g] :
    (grMapCyclesIsoKernelObj S φ).hom ≫ (grMap φ).map (kernelι S.g) = (S.map (grMap φ)).iCycles :=
  (grMapLeftHomologyData S φ).cyclesIso_hom_comp_i

/-- `gr_φ(Ker β) ≅ cycles(gr_φ S) ⟶ gr_φ(B)` is `gr_φ` of the inclusion `Ker β ⟶ B`. -/
@[reassoc (attr := simp)]
lemma grMapCyclesIsoKernelObj_inv_comp_iCycles [IsStrict S.f] [IsStrict S.g] :
    (grMapCyclesIsoKernelObj S φ).inv ≫ (S.map (grMap φ)).iCycles = (grMap φ).map (kernelι S.g) :=
  (grMapLeftHomologyData S φ).cyclesIso_inv_comp_iCycles

/-- Stacks 0128: `gr_φ(Ker β / Im α) ≅ Ker(gr_φ β) / Im(gr_φ α)`, along any index arrow, for any
index category; the right-hand side is Mathlib's homology of the short complex `gr_φ(S)`. -/
@[stacks 0128 "`gr(Ker β / Im α) = Ker(gr β) / Im(gr α)`, along any index arrow, any `I`"]
noncomputable def grMapHomologyIso [IsStrict S.f] [IsStrict S.g] :
    (grMap φ).obj (homologyObj S) ≅ (S.map (grMap φ)).homology :=
  (grMapLeftHomologyData S φ).homologyIso.symm

/-- `grMapHomologyIso` is compatible with the projections: `gr_φ(Ker β) ⟶ gr_φ(Ker β / Im α) ≅
H(gr_φ S)` is `gr_φ(Ker β) ≅ cycles(gr_φ S) ⟶ H(gr_φ S)`. -/
@[reassoc (attr := simp)]
lemma grMap_map_homologyπObj_comp_grMapHomologyIso_hom [IsStrict S.f] [IsStrict S.g] :
    (grMap φ).map (homologyπObj S) ≫ (grMapHomologyIso S φ).hom =
      (grMapCyclesIsoKernelObj S φ).inv ≫ (S.map (grMap φ)).homologyπ :=
  (grMapLeftHomologyData S φ).π_comp_homologyIso_inv

/-- `grMapHomologyIso` is compatible with the projections: `cycles(gr_φ S) ⟶ H(gr_φ S) ≅
gr_φ(Ker β / Im α)` is `cycles(gr_φ S) ≅ gr_φ(Ker β) ⟶ gr_φ(Ker β / Im α)`. -/
@[reassoc (attr := simp)]
lemma homologyπ_comp_grMapHomologyIso_inv [IsStrict S.f] [IsStrict S.g] :
    (S.map (grMap φ)).homologyπ ≫ (grMapHomologyIso S φ).inv =
      (grMapCyclesIsoKernelObj S φ).hom ≫ (grMap φ).map (homologyπObj S) :=
  (grMapLeftHomologyData S φ).homologyπ_comp_homologyIso_hom

/-- Stacks 0128 in its literal form: `gr_φ(Ker β / Im α) ≅ Coker(gr_φ A ⟶ Ker(gr_φ β))`, i.e.
`grMapHomologyIso` followed by Mathlib's `homologyIsoCokernelLift` for `gr_φ(S)`, with
`Ker(gr_φ β) / Im(gr_φ α)` spelled `cokernel (kernel.lift (gr_φ β) (gr_φ α) _)`. -/
noncomputable def grMapHomologyIsoCokernelLift [IsStrict S.f] [IsStrict S.g] :
    (grMap φ).obj (homologyObj S) ≅
      cokernel (kernel.lift ((grMap φ).map S.g) ((grMap φ).map S.f) (S.map (grMap φ)).zero) :=
  grMapHomologyIso S φ ≪≫ (S.map (grMap φ)).homologyIsoCokernelLift

end Graded

section GradedZ

variable [Abelian C] (S : ShortComplex (FilteredObject C ℤᵒᵖ)) [IsStrict S.f] [IsStrict S.g]

/-- Stacks 0128 in Stacks' indexing: `gr^p(Ker β / Im α) ≅ Ker(gr^p β) / Im(gr^p α)` for every
`p`, for a complex of filtered objects over `ℤᵒᵖ` with `α`, `β` strict. -/
@[stacks 0128 "in Stacks' indexing, `gr^p(Ker β / Im α) = Ker(gr^p β) / Im(gr^p α)`"]
noncomputable def grHomologyIso (p : ℤ) :
    (gr p).obj (homologyObj S) ≅ (S.map (gr p)).homology :=
  grMapHomologyIso S (succHom p)

/-- Stacks 0128 in `Gr(𝒜)`: `gr(Ker β / Im α) ≅ Ker(gr β) / Im(gr α)` as graded objects, the
right-hand side being the homology of `gr(S)` in `Gr(𝒜)` (computed degreewise, as the exact
functor `GradedObject.eval p` preserves homology). -/
@[stacks 0128 "in `Gr(𝒜)`: `gr(Ker β / Im α) = Ker(gr β) / Im(gr α)` as graded objects"]
noncomputable def grGradedHomologyIso :
    grGraded.obj (homologyObj S) ≅ (S.map grGraded).homology :=
  GradedObject.isoMk _ _ fun p =>
    grHomologyIso S p ≪≫ (S.map grGraded).mapHomologyIso (GradedObject.eval p)

end GradedZ

end FilteredObject

end CategoryTheory
