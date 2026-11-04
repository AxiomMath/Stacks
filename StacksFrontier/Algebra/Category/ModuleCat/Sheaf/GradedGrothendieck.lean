module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedDegreeLimits
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedForgetRightAdjoint
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedModuleAbelian
public import StacksCore.Tactic.StacksAttribute

/-!
# The differential graded hull is the shifted cokernel of its unit, and preserves injections

Let `R` be a sheaf of rings on a site and let `A` be a sheaf of differential graded
`R`-algebras. `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedForgetRightAdjoint` exhibits
the functor `SheafOfModules.forgetToGradedModule A` which forgets the differential of a right
differential graded `A`-module as a right adjoint (Tag 0FSK), its left adjoint being the
*differential graded hull* `Hull.obj N`, which in degree `n` is `Nⁿ⁻¹ ⊕ Nⁿ` with differential
`(x, y) ↦ (0, x)`; it also proves parts (1) and (3) of
[Stacks, Tag 0FSL](https://stacks.math.columbia.edu/tag/0FSL), that the unit of that adjunction
is a monomorphism and that the hull is acyclic.

This file proves the two remaining assertions of Tag 0FSL:

* part (2), that the differential induces an isomorphism `N ≅ Coker(N ⟶ F(G(N)))[1]`, and
* the last sentence, that the hull of a monomorphism of graded modules is a monomorphism.

## Main definitions

* `SheafOfModules.GradedModule.shiftHom` is the shift `φ[k]` of a homomorphism of graded
  modules, and `SheafOfModules.GradedModule.unshift` the canonical isomorphism
  `N ≅ (N[-1])[1]`.
* `SheafOfModules.GradedModule.ShiftedHom M N k` is a homomorphism `M ⟶ N[k]` presented by its
  homogeneous components, with the graded-linearity law stated as a heterogeneous equality
  because the two target degrees `n + k + i` and `n + i + k` are only propositionally equal;
  `SheafOfModules.GradedModule.ShiftedHom.ofHom` produces one from a homomorphism into `N[k]`.
* `SheafOfModules.Hull.projPiece`, `sectPiece`, `retrPiece` and `dPiece` are the biproduct
  coordinate maps and the differential of the degree-`n` piece of the hull, and
  `SheafOfModules.Hull.proj` the projection onto the first coordinate as a homomorphism of
  graded modules; `SheafOfModules.Hull.hullUnit` is the unit of the hull adjunction.
* `SheafOfModules.hullUniq` is the canonical isomorphism between the hull functor and the left
  adjoint chosen by the `IsRightAdjoint` instance of Tag 0FSK, `SheafOfModules.hullCompIso` its
  image under forgetting differentials, `SheafOfModules.chosenUnit` and
  `SheafOfModules.dChosen` the unit and the differential of that chosen left adjoint, and
  `SheafOfModules.projChosen` the hull's projection transported to it.
* `SheafOfModules.cokerShiftCompare` is the comparison from the cokernel of the unit to the
  shift `N[-1]`.
* `SheafOfModules.cofreeFunctor` is the cofree differential graded module as a functor, with
  `SheafOfModules.cofreeAdjunction` the adjunction of
  `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedForgetColimits`, and
  `SheafOfModules.hullMap` is its action on the shift of a graded homomorphism, read as a
  morphism of hulls.

## Main results

* `SheafOfModules.dgHull_differential_cokernel_iso` is **Tag 0FSL part (2)**: there is a
  homomorphism `N ⟶ Coker(N ⟶ F(G(N)))[1]` which is an isomorphism in every homogeneous degree
  and is given there by the unit followed by the differential and the projection to the
  cokernel.
* `SheafOfModules.dgHull_map_mono` is **the last assertion of Tag 0FSL**: the hull of a
  monomorphism of graded modules is a monomorphism.
* `SheafOfModules.isIso_cokerShiftCompare` is the content behind part (2): the cokernel of the
  unit is the shift `N[-1]`.
* `SheafOfModules.Hull.isColimitCokernelCoforkProjPiece`: in every degree, the projection of
  the hull onto its first coordinate is a cokernel of the inclusion of `N`.
* `SheafOfModules.dgHullFunctor_map_eq`: the hull functor acts on morphisms as the cofree
  functor on the shift by `-1`.

## Implementation notes

**The hypotheses.** Part (2) mentions the cokernel of the unit, so it needs graded modules to
have cokernels; those are supplied by
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedModuleAbelian` under
`HasSheafify J AddCommGrpCat` and `J.WEqualsLocallyBijective AddCommGrpCat` at the module
universe, which are the two conditions making `SheafOfModules` abelian and are the standing
convention of the source that a site admits sheafification. The last assertion needs no
hypothesis at all. No universe is specialized: the site, the sheaf of rings, the algebra
components and the module components keep the four independent universes of
`GradedForgetColimits`, and `RingedSite.{u, u, u}` with module universe
`max u v w` is the special case `v = u`, `t = u`, `a = v`, `m = max u v w`.

**The `Mono` reflection.** The last assertion of Tag 0FSL needs the *categorical*
monomorphism `i` to give degreewise monomorphisms. That is
`SheafOfModules.GradedModule.mono_app_of_mono`, which holds with no hypothesis on the site
because each `pieceFunctor` preserves finite limits.

**Two spellings of one object, and why every coordinate map is wrapped.** The degree-`n` piece
of the hull is `Cofree.piece (N[-1]) n = Nⁿ⁻¹ ⊞ Nⁿ` when written through the cofree
construction and `((forgetToGradedModule A).obj (Hull.obj N)).piece n` when written through the
graded-module API. The two are definitionally equal but not syntactically so, and `rw`, `simp`
and `kabstract` all refuse a goal that mixes them — the error is the misleading "target
expression is not type-correct under the `implicit` transparency level". Every statement below
is therefore kept in *one* spelling: the biproduct coordinate maps `biprod.fst`, `biprod.inl`
and `biprod.snd` are wrapped in the definitions `Hull.projPiece`, `Hull.sectPiece` and
`Hull.retrPiece`, whose ascribed types are the graded ones, and the differentials in
`Hull.dPiece` and `dChosen`; the adjunction units, whose types otherwise mention the composite
functor `G ⋙ F`, are wrapped in `Hull.hullUnit` and `chosenUnit`. The leaf identities between
the wrappers are proved by unfolding to the biproduct spelling and never rewritten in.

**The chosen left adjoint.** As in `GradedForgetRightAdjoint`, the `IsRightAdjoint` instance
exposes its left adjoint only through `Exists.choose`, so `Functor.leftAdjoint` is not
`dgHullFunctor`. Both results are therefore proved for `dgHullFunctor` and
`dgHullAdjunction` and then transported along `Adjunction.leftAdjointUniq`, part (2) through
`Adjunction.unit_leftAdjointUniq_hom_app` and the last assertion through
`CategoryTheory.NatIso.naturality_1`.

**Why the hull preserves injections.** Rather than computing the hull functor on morphisms in
biproduct coordinates, it is identified with the cofree functor on the shift by `-1`. The two
agree on objects on the nose, and they agree on a morphism because the hull adjunction's
hom-bijection makes a morphism out of `Hull.obj N` determined by its composite with the unit,
and that composite is computed from the counit of the *cofree* adjunction together with the one
biproduct identity `Hull.hullUnit_app_comp_dPiece_comp_projPiece`. Injections are then
preserved because `cofreeFunctor` is a right adjoint, and because the shift of a monomorphism
is a monomorphism.

## References

* [Stacks Project, Tag 0FSL](https://stacks.math.columbia.edu/tag/0FSL)
* [Stacks Project, Tag 0FSK](https://stacks.math.columbia.edu/tag/0FSK)
* [Stacks Project, Tag 0FQ1](https://stacks.math.columbia.edu/tag/0FQ1)
* [Stacks Project, Tag 0FR0](https://stacks.math.columbia.edu/tag/0FR0)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe t a m v u

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}

/-- Transport along a reflexive equality of degrees is the identity. -/
theorem degCastHom_eq_id (X : ℤ → SheafOfModules.{m} R) {i : ℤ} (h : i = i) :
    degCastHom X h = 𝟙 (X i) := rfl

/-- Transport along an equality of degrees, read on sections. -/
theorem degCastHom_val_app (X : ℤ → SheafOfModules.{m} R) {i j : ℤ} (h : i = j) (U : Cᵒᵖ)
    (x : (X i).val.obj U) : (degCastHom X h).val.app U x = castHom X h U x := by
  subst h; rfl

namespace GradedModule

variable {A' : GradedAlgebra.{t, a} R}

/-- Every homogeneous component of the zero morphism is zero. -/
@[simp] theorem Hom.zero_app (M N : GradedModule.{t, a, m} A') (n : ℤ) :
    (0 : M ⟶ N).app n = 0 := rfl

/-- The homogeneous components of a composite are the composites of the components. -/
@[simp] theorem Hom.comp_app' {M N P : GradedModule.{t, a, m} A'} (f : M ⟶ N) (g : N ⟶ P)
    (n : ℤ) : (f ≫ g).app n = f.app n ≫ g.app n := rfl

/-- Every homogeneous component of the identity is the identity. -/
@[simp] theorem Hom.id_app' (M : GradedModule.{t, a, m} A') (n : ℤ) :
    (𝟙 M : M ⟶ M).app n = 𝟙 (M.piece n) := rfl

/-- Equal morphisms of graded modules have equal homogeneous components. -/
theorem Hom.congr_app {M N : GradedModule.{t, a, m} A'} {f g : M ⟶ N} (h : f = g) (n : ℤ) :
    f.app n = g.app n := congrArg (fun φ : M ⟶ N ↦ φ.app n) h

/-- Every homogeneous component of an isomorphism of graded modules is an isomorphism. -/
theorem isIso_app {M N : GradedModule.{t, a, m} A'} (f : M ⟶ N) [IsIso f] (n : ℤ) :
    IsIso (f.app n) :=
  ⟨(inv f).app n,
    Hom.congr_app (IsIso.hom_inv_id f) n, Hom.congr_app (IsIso.inv_hom_id f) n⟩

/-- The component of the inverse of an isomorphism, followed by the component of the
isomorphism, is the identity. -/
@[reassoc]
theorem inv_app_comp_app {M N : GradedModule.{t, a, m} A'} (f : M ⟶ N) [IsIso f] (n : ℤ) :
    (inv f).app n ≫ f.app n = 𝟙 (N.piece n) :=
  Hom.congr_app (IsIso.inv_hom_id f) n

/-- The component of an isomorphism, followed by the component of its inverse, is the
identity. -/
@[reassoc]
theorem app_comp_inv_app {M N : GradedModule.{t, a, m} A'} (f : M ⟶ N) [IsIso f] (n : ℤ) :
    f.app n ≫ (inv f).app n = 𝟙 (M.piece n) :=
  Hom.congr_app (IsIso.hom_inv_id f) n

/-- A graded morphism commutes with transport along an equality of degrees. -/
theorem hom_app_castHom {X Y : GradedModule.{t, a, m} A'} (φ : X ⟶ Y) {k k' : ℤ} (h : k = k')
    (U : Cᵒᵖ) (z : (X.piece k).val.obj U) :
    (φ.app k').val.app U (castHom X.piece h U z)
      = castHom Y.piece h U ((φ.app k).val.app U z) := by
  subst h; rfl

/-- The shift of a graded morphism: in degree `n` it is the degree-`n + k` component. -/
def shiftHom {X Y : GradedModule.{t, a, m} A'} (φ : X ⟶ Y) (k : ℤ) : X.shift k ⟶ Y.shift k where
  app n := φ.app (n + k)
  map_smul n i U x y := by
    rw [shift_smul, shift_smul, hom_app_castHom, φ.map_smul]

/-- The degree-`n` component of `φ[k]` is the degree-`n + k` component of `φ`. -/
@[simp] theorem shiftHom_app {X Y : GradedModule.{t, a, m} A'} (φ : X ⟶ Y) (k n : ℤ) :
    (shiftHom φ k).app n = φ.app (n + k) := rfl

/-- The shift of the identity is the identity. -/
@[simp] theorem shiftHom_id (X : GradedModule.{t, a, m} A') (k : ℤ) :
    shiftHom (𝟙 X) k = 𝟙 (X.shift k) := rfl

/-- The shift of a composite is the composite of the shifts. -/
@[simp] theorem shiftHom_comp {X Y Z : GradedModule.{t, a, m} A'} (φ : X ⟶ Y) (ψ : Y ⟶ Z)
    (k : ℤ) : shiftHom (φ ≫ ψ) k = shiftHom φ k ≫ shiftHom ψ k := rfl

/-- The canonical morphism from a graded module to the shift by `1` of its shift by `-1`. It is
an isomorphism, being a transport along an equality of degrees in each component. -/
def unshift (X : GradedModule.{t, a, m} A') : X ⟶ (X.shift (-1)).shift 1 where
  app n := degCastHom X.piece (by omega : n = n + 1 + -1)
  map_smul n i U x y := by
    simp only [degCastHom_val_app, shift_smul, castHom_shift_piece, Cofree.smul_castHom_left,
      Cofree.castHom_castHom]

/-- The degree-`n` component of `unshift X` is the transport along `n = n + 1 + -1`. -/
@[simp] theorem unshift_app (X : GradedModule.{t, a, m} A') (n : ℤ) :
    (unshift X).app n = degCastHom X.piece (by omega : n = n + 1 + -1) := rfl

/-- A morphism of graded modules `M ⟶ N[k]`, expressed in homogeneous components. The
heterogeneous equality identifies the two associatively equal target degrees. -/
structure ShiftedHom (M N : GradedModule.{t, a, m} A') (k : ℤ) where
  /-- The component from degree `n` to degree `n + k`. -/
  app (n : ℤ) : M.piece n ⟶ N.piece (n + k)
  /-- Compatibility with the graded algebra action. -/
  map_smul (n i : ℤ) (U : Cᵒᵖ) (x : (M.piece n).val.obj U) (y : (A'.piece i).val.obj U) :
    HEq ((app (n + i)).val.app U (M.smul n i U x y))
      (N.smul (n + k) i U ((app n).val.app U x) y)

/-- A morphism into the shift `N[k]` read as a shifted morphism. -/
def ShiftedHom.ofHom {M N : GradedModule.{t, a, m} A'} {k : ℤ} (f : M ⟶ N.shift k) :
    ShiftedHom M N k where
  app n := f.app n
  map_smul n i U x y := by
    refine (heq_of_eq (f.map_smul n i U x y)).trans ?_
    rw [shift_smul]
    exact heq_castHom N.piece _ U _

/-- The components of `ShiftedHom.ofHom f` are those of `f`. -/
@[simp] theorem ShiftedHom.ofHom_app {M N : GradedModule.{t, a, m} A'} {k : ℤ}
    (f : M ⟶ N.shift k) (n : ℤ) : (ShiftedHom.ofHom f).app n = f.app n := rfl

end GradedModule

namespace DifferentialGradedModule

variable {A : DifferentialGradedAlgebra.{t, a} R}

/-- A morphism of differential graded modules with monomorphic components is a monomorphism. -/
theorem mono_of_mono_f {M N : DifferentialGradedModule.{t, a, m} A} (f : M ⟶ N)
    (h : ∀ n, Mono (f.toHomologicalComplex.f n)) : Mono f := by
  constructor
  intro Z g g' hgg'
  refine Hom.ext fun n ↦ (cancel_mono (f.toHomologicalComplex.f n)).1 ?_
  exact congrArg (fun φ : Z ⟶ N ↦ φ.toHomologicalComplex.f n) hgg'

end DifferentialGradedModule

/-! ### Transport lemmas for `degCastHom` -/

namespace GradedModule

variable {A' : GradedAlgebra.{t, a} R}

/-- A graded morphism commutes with transport along an equality of degrees. -/
theorem degCastHom_comp_app {M N : GradedModule.{t, a, m} A'} (f : M ⟶ N) {k k' : ℤ}
    (h : k = k') : degCastHom M.piece h ≫ f.app k' = f.app k ≫ degCastHom N.piece h := by
  subst h; simp

end GradedModule

/-! ### The projection of the hull onto its first coordinate -/

namespace Hull

variable {A : DifferentialGradedAlgebra.{t, a} R} (N : GradedModule.{t, a, m} A.toGradedAlgebra)

/-- The inclusion of `N` into its differential graded hull, with the degrees of the biproduct
written in the shape the cofree construction uses. -/
theorem unitHom_eq (n : ℤ) :
    unitHom N n = degCastHom N.piece (show n = n + 1 + -1 by omega)
      ≫ (biprod.inr : (N.shift (-1)).piece (n + 1) ⟶ Cofree.piece (N.shift (-1)) n) := rfl

/-! The four morphisms below are the biproduct coordinate maps of the degree-`n` piece of the
hull, each given the type that the graded-module API produces for it. The biproduct spelling
`Nⁿ⁻¹ ⊞ Nⁿ` and the graded spelling `(forget (hull N)).piece n` are definitionally equal but
not syntactically so, and `rw` refuses a goal that mixes them; wrapping each coordinate map in
a definition with the graded type keeps every statement below in one spelling. -/

/-- The projection of the degree-`n` piece of the hull onto its first coordinate. -/
noncomputable def projPiece (n : ℤ) :
    ((forgetToGradedModule A).obj (obj N)).piece n ⟶ (N.shift (-1)).piece n := biprod.fst

/-- The inclusion of the first coordinate into the degree-`n` piece of the hull. -/
noncomputable def sectPiece (n : ℤ) :
    (N.shift (-1)).piece n ⟶ ((forgetToGradedModule A).obj (obj N)).piece n := biprod.inl

/-- The projection of the degree-`n` piece of the hull onto its second coordinate, which is
the retraction of the inclusion of `N`. -/
noncomputable def retrPiece (n : ℤ) :
    ((forgetToGradedModule A).obj (obj N)).piece n ⟶ N.piece n :=
  (biprod.snd : Cofree.piece (N.shift (-1)) n ⟶ (N.shift (-1)).piece (n + 1))
    ≫ degCastHom N.piece (show n + 1 + -1 = n by omega)

/-- The differential of the hull, typed by the graded module underlying it. -/
noncomputable def dPiece (n : ℤ) :
    ((forgetToGradedModule A).obj (obj N)).piece n
      ⟶ ((forgetToGradedModule A).obj (obj N)).piece (n + 1) :=
  (obj N).complex.d n (n + 1)

/-- The differential of the hull is the differential of the cofree module on `N[-1]`. -/
theorem dPiece_eq (n : ℤ) : dPiece N n = Cofree.d (N.shift (-1)) n :=
  CochainComplex.of_d _ _ n

/-- The unit of the hull adjunction, with its type written without the composite functor, so
that its homogeneous components are typed by the hull itself. -/
noncomputable def hullUnit : N ⟶ (forgetToGradedModule A).obj (obj N) :=
  (dgHullAdjunction A).unit.app N

/-- The degree-`n` component of the unit is the inclusion `unitHom N n` of `N`. -/
theorem hullUnit_app (n : ℤ) : (hullUnit N).app n = unitHom N n := by
  rw [hullUnit, unit_dgHullAdjunction_app]
  exact Category.comp_id _

/-- The projection of the differential graded hull onto its first coordinate, as a morphism of
graded modules: it is the counit of the cofree adjunction at the shift `N[-1]`. -/
noncomputable def proj : (forgetToGradedModule A).obj (obj N) ⟶ N.shift (-1) :=
  Cofree.lowerHom (N.shift (-1)) (𝟙 (obj N))

/-- The degree-`n` component of `proj N` is `projPiece N n`. -/
theorem proj_app (n : ℤ) : (proj N).app n = projPiece N n :=
  Category.id_comp _

/-! The four biproduct identities, stated in the graded spelling and proved by unfolding to the
biproduct one. -/

/-- The inclusion of `N` followed by the first biproduct projection is zero. -/
theorem unitHom_comp_fst (n : ℤ) :
    unitHom N n
        ≫ (biprod.fst : Cofree.piece (N.shift (-1)) n ⟶ (N.shift (-1)).piece n) = 0 := by
  rw [unitHom_eq]; simp

/-- The inclusion of `N` followed by the second biproduct projection and the degree transport
is the identity. -/
theorem unitHom_comp_snd (n : ℤ) :
    unitHom N n ≫ (biprod.snd : Cofree.piece (N.shift (-1)) n ⟶ (N.shift (-1)).piece (n + 1))
        ≫ degCastHom N.piece (show n + 1 + -1 = n by omega) = 𝟙 (N.piece n) := by
  rw [unitHom_eq]
  simp [degCastHom_comp_degCastHom]

/-- The biproduct decomposition of the identity of the degree-`n` piece of the hull, with the
second summand written through the inclusion of `N`. -/
theorem biprod_total_unitHom (n : ℤ) :
    ((biprod.snd : Cofree.piece (N.shift (-1)) n ⟶ (N.shift (-1)).piece (n + 1))
          ≫ degCastHom N.piece (show n + 1 + -1 = n by omega)) ≫ unitHom N n
        + biprod.fst ≫ biprod.inl
      = 𝟙 (Cofree.piece (N.shift (-1)) n) := by
  rw [unitHom_eq, Category.assoc, ← Category.assoc (degCastHom _ _),
    degCastHom_comp_degCastHom, degCastHom_eq_id, Category.id_comp, add_comm, biprod.total]

/-- The unit followed by the projection onto the first coordinate is zero. -/
theorem hullUnit_app_comp_projPiece (n : ℤ) : (hullUnit N).app n ≫ projPiece N n = 0 := by
  rw [hullUnit_app]
  exact unitHom_comp_fst N n

/-- The unit followed by the projection onto the second coordinate is the identity. -/
theorem hullUnit_app_comp_retrPiece (n : ℤ) :
    (hullUnit N).app n ≫ retrPiece N n = 𝟙 (N.piece n) := by
  rw [hullUnit_app]
  exact unitHom_comp_snd N n

/-- The inclusion of the first coordinate followed by the projection onto it is the
identity. -/
theorem sectPiece_comp_projPiece (n : ℤ) :
    sectPiece N n ≫ projPiece N n = 𝟙 ((N.shift (-1)).piece n) := biprod.inl_fst

/-- The projection onto the first coordinate is an epimorphism. -/
instance epi_projPiece (n : ℤ) : Epi (projPiece N n) :=
  epi_of_epi_fac (sectPiece_comp_projPiece N n)

/-- The biproduct decomposition of the identity of the degree-`n` piece of the hull through the
unit and the two coordinate maps. -/
theorem retrPiece_add (n : ℤ) :
    retrPiece N n ≫ (hullUnit N).app n + projPiece N n ≫ sectPiece N n
      = 𝟙 (((forgetToGradedModule A).obj (obj N)).piece n) := by
  rw [hullUnit_app]
  exact biprod_total_unitHom N n

/-- The unit followed by the projection of the hull onto `N[-1]` is zero. -/
theorem hullUnit_comp_proj : hullUnit N ≫ proj N = 0 :=
  GradedModule.Hom.ext fun n ↦ by
    rw [GradedModule.Hom.comp_app', proj_app, hullUnit_app_comp_projPiece,
      GradedModule.Hom.zero_app]

/-- **In every degree the projection onto the first coordinate is a cokernel of the inclusion
of `N` into its hull.** The degree-`n` piece of the hull is the biproduct of `Nⁿ⁻¹` with `Nⁿ`,
the inclusion is the second summand and the projection is onto the first, so the sequence is
split exact. -/
noncomputable def isColimitCokernelCoforkProjPiece (n : ℤ) :
    IsColimit (CokernelCofork.ofπ (f := (hullUnit N).app n) (projPiece N n)
      (hullUnit_app_comp_projPiece N n)) :=
  CokernelCofork.IsColimit.ofπ _ _
    (fun {_} g' _ ↦ sectPiece N n ≫ g')
    (fun {_} g' w' ↦ by
      calc projPiece N n ≫ sectPiece N n ≫ g'
          = (retrPiece N n ≫ (hullUnit N).app n + projPiece N n ≫ sectPiece N n) ≫ g' := by
            rw [Preadditive.add_comp, Category.assoc, Category.assoc, w', comp_zero, zero_add]
        _ = g' := by rw [retrPiece_add, Category.id_comp])
    (fun {_} _ _ m hm ↦ by
      rw [← hm, ← Category.assoc, sectPiece_comp_projPiece, Category.id_comp])

/-- The composite of the inclusion of `N` into its hull, the differential, and the projection
onto the first coordinate is the canonical degree transport. This is the computation behind
Tag 0FSL part (2). -/
theorem unitHom_comp_cofreeD_comp_fst (n : ℤ) :
    unitHom N n ≫ Cofree.d (N.shift (-1)) n ≫ biprod.fst
      = degCastHom N.piece (show n = n + 1 + -1 by omega) := by
  rw [Cofree.d, unitHom_eq]; simp

/-- The differential of the hull followed by the projection onto the first coordinate is the
projection onto the second biproduct summand. -/
theorem dPiece_comp_projPiece (n : ℤ) :
    dPiece N n ≫ projPiece N (n + 1)
      = (biprod.snd : Cofree.piece (N.shift (-1)) n ⟶ (N.shift (-1)).piece (n + 1)) := by
  rw [dPiece_eq]
  exact (by simp [Cofree.d] :
    Cofree.d (N.shift (-1)) n ≫ (biprod.fst : Cofree.piece (N.shift (-1)) (n + 1)
      ⟶ (N.shift (-1)).piece (n + 1)) = biprod.snd)

/-- Two morphisms into the degree-`n` piece of the hull agree as soon as they agree after the
projection onto the first coordinate and after the differential followed by that projection:
those are the two biproduct coordinates. -/
theorem hom_ext_piece {Z : SheafOfModules.{m} R} (n : ℤ)
    (f g : Z ⟶ ((forgetToGradedModule A).obj (obj N)).piece n)
    (h₁ : f ≫ projPiece N n = g ≫ projPiece N n)
    (h₂ : f ≫ dPiece N n ≫ projPiece N (n + 1)
      = g ≫ dPiece N n ≫ projPiece N (n + 1)) : f = g := by
  rw [dPiece_comp_projPiece] at h₂
  exact biprod.hom_ext _ _ h₁ h₂

/-- The unit, followed by the differential of the hull and the projection onto the first
coordinate, is the canonical degree transport. -/
@[reassoc]
theorem hullUnit_app_comp_dPiece_comp_projPiece (n : ℤ) :
    (hullUnit N).app n ≫ dPiece N n ≫ projPiece N (n + 1)
      = degCastHom N.piece (show n = n + 1 + -1 by omega) := by
  rw [hullUnit_app, dPiece_eq]
  exact unitHom_comp_cofreeD_comp_fst N n

/-- The graded morphism attached to a morphism out of the hull is the unit followed by the
morphism with its differential forgotten. -/
theorem lowerHom_eq {M : DifferentialGradedModule.{t, a, m} A} (ψ : obj N ⟶ M) :
    lowerHom N ψ = hullUnit N ≫ (forgetToGradedModule A).map ψ :=
  GradedModule.Hom.ext fun n ↦ by
    rw [GradedModule.Hom.comp_app', hullUnit_app]
    exact rfl

/-- The morphism of differential graded modules that the hull functor assigns to a graded
morphism is characterized by the unit. -/
theorem lowerHom_dgHullFunctor_map {N' : GradedModule.{t, a, m} A.toGradedAlgebra}
    (i : N ⟶ N') : lowerHom N ((dgHullFunctor A).map i) = i ≫ hullUnit N' := by
  refine Eq.trans ((homEquiv N (obj N')).apply_symm_apply _) ?_
  rw [hullUnit, unit_dgHullAdjunction_app]
  exact rfl

end Hull

/-! ### Tag 0FSL, part (2) -/

variable {A : DifferentialGradedAlgebra.{t, a} R}

/-- The canonical isomorphism from the differential graded hull functor to the left adjoint
chosen by the `IsRightAdjoint` instance of Tag 0FSK. -/
noncomputable def hullUniq (A : DifferentialGradedAlgebra.{t, a} R) :
    dgHullFunctor.{t, a, m} A ≅ (forgetToGradedModule.{t, a, m} A).leftAdjoint :=
  Adjunction.leftAdjointUniq (dgHullAdjunction A)
    (Adjunction.ofIsRightAdjoint (forgetToGradedModule.{t, a, m} A))

variable (N : GradedModule.{t, a, m} A.toGradedAlgebra)

/-- The comparison of the differential graded hull with the chosen left adjoint, after
forgetting differentials. -/
noncomputable def hullCompIso : (forgetToGradedModule A).obj (Hull.obj N)
    ≅ (forgetToGradedModule A).obj ((forgetToGradedModule A).leftAdjoint.obj N) :=
  (forgetToGradedModule A).mapIso ((hullUniq A).app N)

/-- The components of `hullCompIso N` and of its inverse compose to the identity. -/
@[reassoc]
theorem hullCompIso_hom_app_comp_inv_app (n : ℤ) :
    (hullCompIso N).hom.app n ≫ (hullCompIso N).inv.app n = 𝟙 _ := by
  rw [← GradedModule.Hom.comp_app', Iso.hom_inv_id, GradedModule.Hom.id_app']

/-- The components of the inverse of `hullCompIso N` and of `hullCompIso N` compose to the
identity. -/
@[reassoc]
theorem hullCompIso_inv_app_comp_hom_app (n : ℤ) :
    (hullCompIso N).inv.app n ≫ (hullCompIso N).hom.app n = 𝟙 _ := by
  rw [← GradedModule.Hom.comp_app', Iso.inv_hom_id, GradedModule.Hom.id_app']

/-- The differential of the chosen left adjoint, typed by the graded module underlying it. -/
noncomputable def dChosen (n : ℤ) :
    ((forgetToGradedModule A).obj ((forgetToGradedModule A).leftAdjoint.obj N)).piece n
      ⟶ ((forgetToGradedModule A).obj
          ((forgetToGradedModule A).leftAdjoint.obj N)).piece (n + 1) :=
  ((forgetToGradedModule A).leftAdjoint.obj N).complex.d n (n + 1)

/-- The comparison commutes with the differentials. -/
@[reassoc]
theorem hullCompIso_hom_app_comp_dChosen (n : ℤ) :
    (hullCompIso N).hom.app n ≫ dChosen N n
      = Hull.dPiece N n ≫ (hullCompIso N).hom.app (n + 1) :=
  ((hullUniq A).hom.app N).toHomologicalComplex.comm n (n + 1)

/-- The unit of the adjunction chosen by the `IsRightAdjoint` instance, with its type written
without the composite functor. -/
noncomputable def chosenUnit : N ⟶ (forgetToGradedModule A).obj
    ((forgetToGradedModule A).leftAdjoint.obj N) :=
  (Adjunction.ofIsRightAdjoint (forgetToGradedModule A)).unit.app N

/-- The chosen unit is the hull unit followed by the comparison `hullCompIso N`. -/
theorem chosenUnit_eq : chosenUnit N = Hull.hullUnit N ≫ (hullCompIso N).hom :=
  (Adjunction.unit_leftAdjointUniq_hom_app (dgHullAdjunction A)
    (Adjunction.ofIsRightAdjoint (forgetToGradedModule A)) N).symm

/-- The degree-`n` component of the chosen unit is that of the hull unit followed by that of
the comparison `hullCompIso N`. -/
theorem chosenUnit_app (n : ℤ) :
    (chosenUnit N).app n = (Hull.hullUnit N).app n ≫ (hullCompIso N).hom.app n := by
  rw [chosenUnit_eq, GradedModule.Hom.comp_app']

/-- The projection of the hull onto `N[-1]`, transported to the chosen left adjoint. -/
noncomputable def projChosen : (forgetToGradedModule A).obj
    ((forgetToGradedModule A).leftAdjoint.obj N) ⟶ N.shift (-1) :=
  (hullCompIso N).inv ≫ Hull.proj N

/-- The degree-`n` component of `projChosen N` is the inverse comparison followed by the
projection onto the first coordinate. -/
theorem projChosen_app (n : ℤ) :
    (projChosen N).app n = (hullCompIso N).inv.app n ≫ Hull.projPiece N n := by
  rw [projChosen, GradedModule.Hom.comp_app', Hull.proj_app]

/-- The chosen unit followed by the transported projection onto `N[-1]` is zero. -/
theorem chosenUnit_comp_projChosen : chosenUnit N ≫ projChosen N = 0 := by
  rw [chosenUnit_eq, projChosen, Category.assoc, ← Category.assoc (hullCompIso N).hom,
    Iso.hom_inv_id, Category.id_comp, Hull.hullUnit_comp_proj]

section Cokernel

variable [HasSheafify J AddCommGrpCat.{m}] [J.WEqualsLocallyBijective AddCommGrpCat.{m}]

/-- The comparison from the cokernel of the chosen unit to the shift `N[-1]`. -/
noncomputable def cokerShiftCompare : cokernel (chosenUnit N) ⟶ N.shift (-1) :=
  cokernel.desc _ (projChosen N) (chosenUnit_comp_projChosen N)

/-- In every degree, the projection to the cokernel followed by `cokerShiftCompare N` is
`projChosen N`. -/
@[reassoc]
theorem cokernel_π_app_comp_cokerShiftCompare_app (n : ℤ) :
    (cokernel.π (chosenUnit N)).app n ≫ (cokerShiftCompare N).app n
      = (projChosen N).app n := by
  rw [← GradedModule.Hom.comp_app', cokerShiftCompare, cokernel.π_desc]

/-- **The cokernel of the unit is the shift `N[-1]`.** The comparison is an isomorphism because
it is one in every homogeneous degree, where both sides are cokernels of the same morphism. -/
instance isIso_cokerShiftCompare : IsIso (cokerShiftCompare N) := by
  refine GradedModule.isIso_of_componentwise _ fun n ↦ ?_
  have hc := isColimitOfHasCokernelOfPreservesColimit
    (GradedModule.pieceFunctor A.toGradedAlgebra n) (chosenUnit N)
  have hepi : Epi ((cokernel.π (chosenUnit N)).app n) := Cofork.IsColimit.epi hc
  have hu := Hull.isColimitCokernelCoforkProjPiece N n
  have hzero : (chosenUnit N).app n ≫ (cokernel.π (chosenUnit N)).app n = 0 := by
    rw [← GradedModule.Hom.comp_app', cokernel.condition, GradedModule.Hom.zero_app]
  have hcond : (Hull.hullUnit N).app n ≫ ((hullCompIso N).hom.app n
      ≫ (cokernel.π (chosenUnit N)).app n)
      = 0 ≫ ((hullCompIso N).hom.app n ≫ (cokernel.π (chosenUnit N)).app n) := by
    rw [zero_comp, ← Category.assoc, ← chosenUnit_app]
    exact hzero
  have h1 := Cofork.IsColimit.π_desc' hu _ hcond
  rw [Cofork.π_ofπ] at h1
  refine ⟨Cofork.IsColimit.desc hu _ hcond, ?_, ?_⟩
  · refine (cancel_epi ((cokernel.π (chosenUnit N)).app n)).1 ?_
    rw [Category.comp_id, ← Category.assoc, cokernel_π_app_comp_cokerShiftCompare_app,
      projChosen_app, Category.assoc, h1, ← Category.assoc,
      hullCompIso_inv_app_comp_hom_app, Category.id_comp]
  · refine (cancel_epi (Hull.projPiece N n)).1 ?_
    rw [Category.comp_id, ← Category.assoc, h1, Category.assoc,
      cokernel_π_app_comp_cokerShiftCompare_app, projChosen_app, ← Category.assoc,
      hullCompIso_hom_app_comp_inv_app, Category.id_comp]

/-- The homogeneous components of the isomorphism of Tag 0FSL part (2). -/
theorem shiftedHom_app_eq (n : ℤ) :
    (GradedModule.ShiftedHom.ofHom (GradedModule.unshift N
        ≫ GradedModule.shiftHom (inv (cokerShiftCompare N)) 1)).app n
      = degCastHom N.piece (show n = n + 1 + -1 by omega)
        ≫ (inv (cokerShiftCompare N)).app (n + 1) := rfl

/-- Tag 0FSL part (2), in the vocabulary of `chosenUnit` and `dChosen`. -/
theorem exists_shiftedHom_cokernel_chosenUnit :
    ∃ f : GradedModule.ShiftedHom N (cokernel (chosenUnit N)) 1,
      (∀ n : ℤ, IsIso (f.app n)) ∧
      (∀ n : ℤ, HEq (f.app n)
        ((chosenUnit N).app n ≫ dChosen N n
          ≫ (cokernel.π (chosenUnit N)).app (n + 1))) := by
  refine ⟨GradedModule.ShiftedHom.ofHom (GradedModule.unshift N
    ≫ GradedModule.shiftHom (inv (cokerShiftCompare N)) 1), fun n ↦ ?_, fun n ↦ ?_⟩
  · have h2 : IsIso ((inv (cokerShiftCompare N)).app (n + 1)) :=
      GradedModule.isIso_app _ _
    rw [shiftedHom_app_eq]
    infer_instance
  · have hiso : IsIso ((cokerShiftCompare N).app (n + 1)) := GradedModule.isIso_app _ _
    have hL : (degCastHom N.piece (show n = n + 1 + -1 by omega)
          ≫ (inv (cokerShiftCompare N)).app (n + 1)) ≫ (cokerShiftCompare N).app (n + 1)
        = degCastHom N.piece (show n = n + 1 + -1 by omega) := by
      rw [Category.assoc, GradedModule.inv_app_comp_app]
      exact Category.comp_id _
    refine heq_of_eq ((cancel_mono ((cokerShiftCompare N).app (n + 1))).1 ?_)
    rw [shiftedHom_app_eq, hL, Category.assoc, Category.assoc,
      cokernel_π_app_comp_cokerShiftCompare_app, projChosen_app, chosenUnit_app,
      Category.assoc, ← Category.assoc ((hullCompIso N).hom.app n),
      hullCompIso_hom_app_comp_dChosen, Category.assoc,
      hullCompIso_hom_app_comp_inv_app_assoc,
      Hull.hullUnit_app_comp_dPiece_comp_projPiece]

/-- **Tag 0FSL, part (2).** The differential of the differential graded hull induces an
isomorphism from a graded module to the shift by one of the cokernel of the adjunction unit;
in each homogeneous degree it is the unit followed by the differential and the projection to
the cokernel. -/
@[stacks 0FSL "part (2)"]
theorem dgHull_differential_cokernel_iso :
    ∃ f : GradedModule.ShiftedHom N (cokernel ((Adjunction.ofIsRightAdjoint
        (forgetToGradedModule.{t, a, m} A)).unit.app N)) 1,
      (∀ n : ℤ, IsIso (f.app n)) ∧
      (∀ n : ℤ, HEq (f.app n)
        (((Adjunction.ofIsRightAdjoint (forgetToGradedModule.{t, a, m} A)).unit.app N).app n
          ≫ ((forgetToGradedModule.{t, a, m} A).leftAdjoint.obj N).complex.d n (n + 1)
          ≫ (cokernel.π ((Adjunction.ofIsRightAdjoint
              (forgetToGradedModule.{t, a, m} A)).unit.app N)).app (n + 1))) :=
  exists_shiftedHom_cokernel_chosenUnit N

end Cokernel

/-! ### The hull preserves injections -/

section Injections

variable {X Y : GradedModule.{t, a, m} A.toGradedAlgebra}

/-- The cofree differential graded module as a functor: the right adjoint to forgetting the
differential, i.e. the one `SheafOfModules.forgetAdjunction` produces. -/
noncomputable def cofreeFunctor (A : DifferentialGradedAlgebra.{t, a} R) :
    GradedModule.{t, a, m} A.toGradedAlgebra ⥤ DifferentialGradedModule.{t, a, m} A :=
  Adjunction.rightAdjointOfEquiv Cofree.homEquiv Cofree.homEquiv_naturality

/-- Forgetting the differential is left adjoint to the cofree functor. -/
noncomputable def cofreeAdjunction (A : DifferentialGradedAlgebra.{t, a} R) :
    forgetToGradedModule.{t, a, m} A ⊣ cofreeFunctor.{t, a, m} A :=
  forgetAdjunction A

/-- The cofree functor on the shift by `-1` of a graded morphism, read as a morphism of hulls.
The hull of `N` *is* the cofree module on `N[-1]`, so this is the same morphism; what the
definition fixes is the spelling of its source and target. -/
noncomputable def hullMap (i : X ⟶ Y) : Hull.obj X ⟶ Hull.obj Y :=
  (cofreeFunctor A).map (GradedModule.shiftHom i (-1))

/-- A right adjoint preserves monomorphisms, so the hull of an injection is an injection. -/
theorem mono_hullMap (i : X ⟶ Y) [Mono i] [Mono (GradedModule.shiftHom i (-1))] :
    Mono (hullMap i) := by
  have h : PreservesLimitsOfSize.{0, 0} (cofreeFunctor.{t, a, m} A) :=
    (cofreeAdjunction A).rightAdjoint_preservesLimits
  have : (cofreeFunctor.{t, a, m} A).PreservesMonomorphisms :=
    preservesMonomorphisms_of_preservesLimitsOfShape _
  exact Functor.map_mono (cofreeFunctor A) (GradedModule.shiftHom i (-1))

/-- Forgetting the differential of a morphism into a cofree module and composing with the
counit recovers the graded morphism the cofree adjunction attaches to it. -/
theorem forget_map_comp_lowerHom_id {P : GradedModule.{t, a, m} A.toGradedAlgebra}
    {M : DifferentialGradedModule.{t, a, m} A} (ψ : M ⟶ Cofree.cofree P) :
    (forgetToGradedModule A).map ψ ≫ Cofree.lowerHom P (𝟙 (Cofree.cofree P))
      = Cofree.lowerHom P ψ :=
  GradedModule.Hom.ext fun n ↦ congrArg (fun φ ↦ ψ.toHomologicalComplex.f n ≫ φ)
    (Category.id_comp (biprod.fst : Cofree.piece P n ⟶ P.piece n))

/-- The square relating the hull of a morphism to the projections onto the first
coordinate. -/
theorem forget_hullMap_comp_proj (i : X ⟶ Y) :
    (forgetToGradedModule A).map (hullMap i) ≫ Hull.proj Y
      = Hull.proj X ≫ GradedModule.shiftHom i (-1) :=
  (forget_map_comp_lowerHom_id _).trans (Cofree.lowerHom_liftDgHom _ _)

/-- The degree-`n` component of the hull of a morphism. -/
noncomputable def hullMapPiece (i : X ⟶ Y) (n : ℤ) :
    ((forgetToGradedModule A).obj (Hull.obj X)).piece n
      ⟶ ((forgetToGradedModule A).obj (Hull.obj Y)).piece n :=
  ((forgetToGradedModule A).map (hullMap i)).app n

/-- The degree-`n` component of the hull of a morphism, with differentials forgotten, is
`hullMapPiece i n`. -/
theorem hullMapPiece_eq (i : X ⟶ Y) (n : ℤ) :
    ((forgetToGradedModule A).map (hullMap i)).app n = hullMapPiece i n := rfl

/-- The degree-`n` component of the hull of `i` commutes with the projections onto the first
coordinate, through the degree-`n` component of `i[-1]`. -/
@[reassoc]
theorem hullMapPiece_comp_projPiece (i : X ⟶ Y) (n : ℤ) :
    hullMapPiece i n ≫ Hull.projPiece Y n
      = Hull.projPiece X n ≫ (GradedModule.shiftHom i (-1)).app n := by
  have h2 := GradedModule.Hom.congr_app (forget_hullMap_comp_proj i) n
  rw [GradedModule.Hom.comp_app', GradedModule.Hom.comp_app', Hull.proj_app,
    Hull.proj_app] at h2
  exact h2

/-- The components of the hull of a morphism commute with the differentials of the hulls. -/
@[reassoc]
theorem hullMapPiece_comp_dPiece (i : X ⟶ Y) (n : ℤ) :
    hullMapPiece i n ≫ Hull.dPiece Y n = Hull.dPiece X n ≫ hullMapPiece i (n + 1) :=
  (hullMap i).toHomologicalComplex.comm n (n + 1)

/-- The unit of the hull adjunction composed with the hull of a morphism is the morphism
composed with the unit: both composites are detected by the two biproduct coordinates of the
hull. -/
theorem hullUnit_comp_forget_hullMap (i : X ⟶ Y) :
    Hull.hullUnit X ≫ (forgetToGradedModule A).map (hullMap i) = i ≫ Hull.hullUnit Y := by
  have hproj : (Hull.hullUnit X ≫ (forgetToGradedModule A).map (hullMap i)) ≫ Hull.proj Y
      = (i ≫ Hull.hullUnit Y) ≫ Hull.proj Y := by
    rw [Category.assoc, forget_hullMap_comp_proj, ← Category.assoc,
      Hull.hullUnit_comp_proj, zero_comp, Category.assoc, Hull.hullUnit_comp_proj, comp_zero]
  refine GradedModule.Hom.ext fun n ↦ Hull.hom_ext_piece Y n _ _ ?_ ?_
  · have h2 := GradedModule.Hom.congr_app hproj n
    rw [GradedModule.Hom.comp_app', GradedModule.Hom.comp_app', Hull.proj_app] at h2
    exact h2
  · rw [GradedModule.Hom.comp_app', GradedModule.Hom.comp_app', hullMapPiece_eq,
      Category.assoc, hullMapPiece_comp_dPiece_assoc, hullMapPiece_comp_projPiece,
      Hull.hullUnit_app_comp_dPiece_comp_projPiece_assoc, GradedModule.shiftHom_app,
      GradedModule.degCastHom_comp_app, Category.assoc,
      Hull.hullUnit_app_comp_dPiece_comp_projPiece]

/-- The hull functor agrees with the cofree functor on the shift by `-1`. -/
theorem dgHullFunctor_map_eq (i : X ⟶ Y) : (dgHullFunctor A).map i = hullMap i := by
  refine (Hull.homEquiv X (Hull.obj Y)).injective ?_
  refine Eq.trans (Hull.lowerHom_dgHullFunctor_map X i) ?_
  refine Eq.trans ?_ (Hull.lowerHom_eq X _).symm
  exact (hullUnit_comp_forget_hullMap i).symm

/-- **Tag 0FSL, the last assertion.** The differential graded hull takes injections of graded
modules to injections of differential graded modules: it is the cofree functor on the shift by
`-1`, and a right adjoint preserves monomorphisms. -/
theorem dgHull_map_mono (i : X ⟶ Y) [Mono i] :
    Mono ((forgetToGradedModule.{t, a, m} A).leftAdjoint.map i) := by
  have hi : ∀ k : ℤ, Mono (i.app k) := fun k ↦ GradedModule.mono_app_of_mono i k
  have hshift : Mono (GradedModule.shiftHom i (-1)) :=
    GradedModule.mono_of_mono_app _ fun n ↦ hi (n + -1)
  have h3 : Mono ((dgHullFunctor A).map i) := by
    rw [dgHullFunctor_map_eq]
    exact mono_hullMap i
  rw [← NatIso.naturality_1 (hullUniq A) i]
  exact mono_comp _ _

end Injections

end SheafOfModules

end
