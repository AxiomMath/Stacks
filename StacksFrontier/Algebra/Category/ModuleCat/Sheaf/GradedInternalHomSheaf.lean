module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedInternalHomSheaf
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedInternalHom
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationTensor
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.CohomologyOfModules
public import StacksCore.Tactic.StacksAttribute

/-!
# The internal hom of sheaves of graded modules, constructed

Let `(C, O)` be a ringed site, let `A` be a sheaf of graded `O`-algebras and let `K`, `L`, `M`
be right graded `A`-modules. Following [Stacks, Tag 0FR3], this file

1. constructs `SheafHom^gr_A(M, L)`, the graded `O`-module whose degree-`n` term
   `SheafHom^n_A(M, L)` is the subsheaf of `∏_i SheafHom_O(M^i, L^{i + n})` of those local
   sections `f = (f_i)` with `f_{i + p}(x a) = f_i(x) a` for local sections `a` of `A^p`;
2. constructs the composition map
   `SheafHom^m_A(L, M) ⊗_O SheafHom^n_A(K, L) ⟶ SheafHom^{n + m}_A(K, M)`, given locally by
   composition, and the induced map out of the degree-`k` term
   `⨁_{m + n = k} SheafHom^m_A(L, M) ⊗_O SheafHom^n_A(K, L)` of the tensor product of graded
   `O`-modules;
3. proves `Hom_{Mod^gr(A)}(L, M) = Γ(C, SheafHom^gr_A(L, M))` as graded `Γ(C, O)`-modules,
   compatibly with composition.

## Main definitions

* `SheafOfModules.gradedLocalHomSheaf M L n`: the sheaf of `O`-modules `SheafHom^n_A(M, L)`,
  whose sections over `U` are the degree-`n` local homomorphisms
  `SheafOfModules.GradedLocalHom M L n U`, and `SheafOfModules.gradedSheafHom M L` the graded
  `O`-module `SheafHom^gr_A(M, L)`.
* `SheafOfModules.GradedLocalHom.comp`: composition of local homomorphisms, and
  `SheafOfModules.gradedSheafHomComp m n` the composition map out of the tensor product of
  sheaves of `O`-modules; `SheafOfModules.gradedSheafHomCompSum k` is the composition map on
  degree `k` of the tensor product of the two graded `O`-modules.
* `SheafOfModules.GradedHomOfDegree.comp`: composition in the graded category
  `Mod^gr(A)` of [Stacks, Tag 0FR1], together with the `Γ(C, O)`-module structure on
  `Hom^n(M, L)`.
* `SheafOfModules.gradedHomLinearEquivSections M L n`: the isomorphism of `Γ(C, O)`-modules
  `Hom^n(M, L) ≅ Γ(C, SheafHom^n_A(M, L))`.

## Main results

* `SheafOfModules.gradedLocalHomPresheaf_isSheaf`: the degree-`n` local homomorphisms form a
  sheaf.
* `SheafOfModules.isGradedSheafHom_gradedSheafHom`: the constructed graded `O`-module *is* the
  internal hom in the sense of `SheafOfModules.IsGradedSheafHom`.
* `SheafOfModules.gradedSheafHomComp_tmul`: the composition map sends `g ⊗ f` to `g ∘ f`.
* `SheafOfModules.gradedHomLinearEquivSections_comp`: the identification of
  `Hom_{Mod^gr(A)}` with global sections is compatible with composition.

## Implementation notes

The module structure `(r f)(x) = r f(x)` needs the rings of sections of `O` to be commutative,
recorded by the instance argument `∀ U, IsMulCommutative (R.obj.obj U)` for the construction of the
sheaf (commutativity is used through `SheafOfModules.LocalHom.ring_mul_comm`); this holds for the
structure sheaf of every ringed site. The composition map uses the tensor product of sheaves of
modules, the sheafification of the objectwise tensor product of presheaves of modules [Stacks, Tag
01CA], which is formed over a sheaf of commutative rings `O`; so from there on the base is
`CategoryTheory.Sheaf.toRingCat J O`, the sheaf of rings underlying `O`. The three graded modules
then live in one universe, so that the three internal homs do, as a morphism out of a tensor product
requires.

The degree-`n` local homomorphisms are written with source `M` and target `L`, matching the
notation `SheafHom^gr_A(M, L)`; the display of [Stacks, Tag 0FR3] writes the factors of the
product as `SheafHom_O(L^{-q}, M^p)`, copying the display of [Stacks, Tag 0FR1] where the
source is called `L`.

## References

* [Stacks Project, Tag 0FR1](https://stacks.math.columbia.edu/tag/0FR1)
* [Stacks Project, Tag 0FR2](https://stacks.math.columbia.edu/tag/0FR2)
* [Stacks Project, Tag 0FR3](https://stacks.math.columbia.edu/tag/0FR3)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

open scoped TensorProduct

universe t a w z s v u

namespace SheafOfModules

section Construction

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  {A : GradedAlgebra.{t, a} R}

namespace GradedLocalHom

variable {M : GradedModule.{t, a, w} A} {L : GradedModule.{t, a, z} A} {n : ℤ} {U : C}

/-! ### The additive group of local homomorphisms -/

/-- The zero local homomorphism. -/
instance : Zero (GradedLocalHom M L n U) where
  zero :=
    { app := fun _ _ _ _ => 0
      map_smul := fun _ _ _ _ r _ => (smul_zero r).symm
      naturality := fun i j hij V W q x => by
        refine Eq.trans ?_ (AddMonoidHom.zero_apply _).symm
        rw [AddMonoidHom.zero_apply, map_zero]
      map_mul := fun i j hij p V x b => by
        simp only [AddMonoidHom.zero_apply, map_zero] }

/-- The pointwise sum of local homomorphisms. -/
instance : Add (GradedLocalHom M L n U) where
  add f g :=
    { app := fun i j hij V => AddMonoidHom.mk' (fun x => f.app i j hij V x + g.app i j hij V x)
        (fun x y => by simp only [map_add]; abel)
      map_smul := fun i j hij V r x => by
        simp only [AddMonoidHom.mk'_apply, f.map_smul, g.map_smul, smul_add]
      naturality := fun i j hij V W q x => by
        simp only [AddMonoidHom.mk'_apply, map_add, f.naturality, g.naturality]
        rfl
      map_mul := fun i j hij p V x b => by
        simp only [AddMonoidHom.mk'_apply]
        rw [f.map_mul i j hij p V x b, g.map_mul i j hij p V x b, map_add,
          AddMonoidHom.add_apply] }

/-- The pointwise negation of a local homomorphism. -/
instance : Neg (GradedLocalHom M L n U) where
  neg f :=
    { app := fun i j hij V => AddMonoidHom.mk' (fun x => -f.app i j hij V x)
        (fun x y => by simp only [map_add]; abel)
      map_smul := fun i j hij V r x => by
        simp only [AddMonoidHom.mk'_apply, f.map_smul, smul_neg]
      naturality := fun i j hij V W q x => by
        simp only [AddMonoidHom.mk'_apply, map_neg, f.naturality]
        rfl
      map_mul := fun i j hij p V x b => by
        simp only [AddMonoidHom.mk'_apply]
        rw [f.map_mul i j hij p V x b, map_neg, AddMonoidHom.neg_apply] }

/-- The pointwise difference of local homomorphisms. -/
instance : Sub (GradedLocalHom M L n U) where
  sub f g :=
    { app := fun i j hij V => AddMonoidHom.mk' (fun x => f.app i j hij V x - g.app i j hij V x)
        (fun x y => by simp only [map_add]; abel)
      map_smul := fun i j hij V r x => by
        simp only [AddMonoidHom.mk'_apply, f.map_smul, g.map_smul, smul_sub]
      naturality := fun i j hij V W q x => by
        simp only [AddMonoidHom.mk'_apply, map_sub, f.naturality, g.naturality]
        rfl
      map_mul := fun i j hij p V x b => by
        simp only [AddMonoidHom.mk'_apply]
        rw [f.map_mul i j hij p V x b, g.map_mul i j hij p V x b, map_sub,
          AddMonoidHom.sub_apply] }

/-- The pointwise multiple of a local homomorphism by a natural number. -/
instance : SMul ℕ (GradedLocalHom M L n U) where
  smul k f :=
    { app := fun i j hij V => AddMonoidHom.mk' (fun x => k • f.app i j hij V x)
        (fun x y => by simp only [map_add, smul_add])
      map_smul := fun i j hij V r x => by
        simp only [AddMonoidHom.mk'_apply, f.map_smul, smul_comm k r]
      naturality := fun i j hij V W q x => by
        simp only [AddMonoidHom.mk'_apply, map_nsmul, f.naturality]
        rfl
      map_mul := fun i j hij p V x b => by
        simp only [AddMonoidHom.mk'_apply]
        rw [f.map_mul i j hij p V x b, map_nsmul, AddMonoidHom.nsmul_apply] }

/-- The pointwise multiple of a local homomorphism by an integer. -/
instance : SMul ℤ (GradedLocalHom M L n U) where
  smul k f :=
    { app := fun i j hij V => AddMonoidHom.mk' (fun x => k • f.app i j hij V x)
        (fun x y => by simp only [map_add, smul_add])
      map_smul := fun i j hij V r x => by
        simp only [AddMonoidHom.mk'_apply, f.map_smul, smul_comm k r]
      naturality := fun i j hij V W q x => by
        simp only [AddMonoidHom.mk'_apply, map_zsmul, f.naturality]
        rfl
      map_mul := fun i j hij p V x b => by
        simp only [AddMonoidHom.mk'_apply]
        rw [f.map_mul i j hij p V x b, map_zsmul, AddMonoidHom.zsmul_apply] }

/-- The zero local homomorphism takes every local section to zero. -/
@[simp] theorem zero_app (i j : ℤ) (hij : i + n = j) (V : Over U)
    (x : (M.piece i).val.obj (op V.left)) :
    (0 : GradedLocalHom M L n U).app i j hij V x = 0 := rfl

/-- The value of a sum of local homomorphisms is the sum of the values. -/
@[simp] theorem add_app (f g : GradedLocalHom M L n U) (i j : ℤ) (hij : i + n = j) (V : Over U)
    (x : (M.piece i).val.obj (op V.left)) :
    (f + g).app i j hij V x = f.app i j hij V x + g.app i j hij V x := rfl

/-- The value of the negation of a local homomorphism is the negation of the value. -/
@[simp] theorem neg_app (f : GradedLocalHom M L n U) (i j : ℤ) (hij : i + n = j) (V : Over U)
    (x : (M.piece i).val.obj (op V.left)) :
    (-f).app i j hij V x = -f.app i j hij V x := rfl

/-- The value of a difference of local homomorphisms is the difference of the values. -/
@[simp] theorem sub_app (f g : GradedLocalHom M L n U) (i j : ℤ) (hij : i + n = j) (V : Over U)
    (x : (M.piece i).val.obj (op V.left)) :
    (f - g).app i j hij V x = f.app i j hij V x - g.app i j hij V x := rfl

/-- The value of `k • f`, for a natural number `k`, is `k` times the value of `f`. -/
@[simp] theorem nsmul_app (k : ℕ) (f : GradedLocalHom M L n U) (i j : ℤ) (hij : i + n = j)
    (V : Over U) (x : (M.piece i).val.obj (op V.left)) :
    (k • f).app i j hij V x = k • f.app i j hij V x := rfl

/-- The value of `k • f`, for an integer `k`, is `k` times the value of `f`. -/
@[simp] theorem zsmul_app (k : ℤ) (f : GradedLocalHom M L n U) (i j : ℤ) (hij : i + n = j)
    (V : Over U) (x : (M.piece i).val.obj (op V.left)) :
    (k • f).app i j hij V x = k • f.app i j hij V x := rfl

/-- The local homomorphisms of degree `n` over `U` form an additive commutative group under
pointwise operations. -/
instance : AddCommGroup (GradedLocalHom M L n U) where
  add_assoc f g h := GradedLocalHom.ext fun i j hij V x => add_assoc _ _ _
  zero_add f := GradedLocalHom.ext fun i j hij V x => zero_add _
  add_zero f := GradedLocalHom.ext fun i j hij V x => add_zero _
  add_comm f g := GradedLocalHom.ext fun i j hij V x => add_comm _ _
  neg_add_cancel f := GradedLocalHom.ext fun i j hij V x => neg_add_cancel _
  sub_eq_add_neg f g := GradedLocalHom.ext fun i j hij V x => sub_eq_add_neg _ _
  nsmul k f := k • f
  zsmul k f := k • f
  nsmul_zero f := GradedLocalHom.ext fun i j hij V x => zero_smul _ _
  nsmul_succ k f := GradedLocalHom.ext fun i j hij V x => succ_nsmul _ _
  zsmul_zero' f := GradedLocalHom.ext fun i j hij V x => zero_smul _ _
  zsmul_succ' k f := GradedLocalHom.ext fun i j hij V x => by
    simp only [zsmul_app, add_app, Int.natCast_succ, add_smul, one_smul, natCast_zsmul]
  zsmul_neg' k f := GradedLocalHom.ext fun i j hij V x => by
    simp only [zsmul_app, neg_app, negSucc_zsmul, natCast_zsmul]

/-! ### The module structure -/

section Module

variable [∀ U : Cᵒᵖ, IsMulCommutative (R.obj.obj U)]

/-- The action `(r f)(x) = r|_V f(x)` of a section `r` of `R` over `U` on a local
homomorphism. -/
instance : SMul (R.obj.obj (op U)) (GradedLocalHom M L n U) where
  smul r f :=
    { app := fun i j hij V => AddMonoidHom.mk'
        (fun x => R.obj.map V.hom.op r • f.app i j hij V x)
        (fun x y => by simp only [map_add, smul_add])
      map_smul := fun i j hij V r' x => by
        simp only [AddMonoidHom.mk'_apply, f.map_smul, smul_smul, LocalHom.ring_mul_comm]
      naturality := fun i j hij V W q x => by
        simp only [AddMonoidHom.mk'_apply]
        rw [PresheafOfModules.map_smul, f.naturality, ← Over.w q, op_comp, Functor.map_comp]
        rfl
      map_mul := fun i j hij p V x b => by
        simp only [AddMonoidHom.mk'_apply]
        rw [f.map_mul i j hij p V x b]
        exact (L.smul_smul_left j p _ _ _ _).symm }

/-- The value of `r • f` over `V` is the restriction of `r` to `V` times the value of `f`. -/
@[simp] theorem smul_app (r : R.obj.obj (op U)) (f : GradedLocalHom M L n U) (i j : ℤ)
    (hij : i + n = j) (V : Over U) (x : (M.piece i).val.obj (op V.left)) :
    (r • f).app i j hij V x = R.obj.map V.hom.op r • f.app i j hij V x := rfl

/-- The local homomorphisms of degree `n` over `U` form a module over the ring of sections of
`R` over `U`. -/
instance : Module (R.obj.obj (op U)) (GradedLocalHom M L n U) where
  one_smul f := GradedLocalHom.ext fun i j hij V x => by
    rw [smul_app, map_one, one_smul]
  mul_smul r r' f := GradedLocalHom.ext fun i j hij V x => by
    rw [smul_app, smul_app, smul_app, _root_.map_mul, mul_smul]
  smul_zero r := GradedLocalHom.ext fun i j hij V x => by
    rw [smul_app, zero_app]
    exact smul_zero _
  smul_add r f g := GradedLocalHom.ext fun i j hij V x => by
    rw [smul_app, add_app, add_app, smul_app, smul_app, smul_add]
  add_smul r r' f := GradedLocalHom.ext fun i j hij V x => by
    rw [smul_app, add_app, smul_app, smul_app, map_add, add_smul]
  zero_smul f := GradedLocalHom.ext fun i j hij V x => by
    rw [smul_app, zero_app, map_zero, zero_smul]

/-- The module structure over the ring of sections at an object of `Cᵒᵖ`. -/
noncomputable instance instModuleUnop (U : Cᵒᵖ) :
    Module (R.obj.obj U) (GradedLocalHom M L n U.unop) :=
  inferInstanceAs (Module (R.obj.obj (op U.unop)) (GradedLocalHom M L n U.unop))

end Module

/-! ### Restriction -/

variable {U' U'' : C}

/-- Restriction of local homomorphisms is additive. -/
theorem restrict_add (g : U' ⟶ U) (f f' : GradedLocalHom M L n U) :
    (f + f').restrict g = f.restrict g + f'.restrict g := rfl

/-- Restriction along `g` is semilinear over the restriction map `R(U) → R(U')`. -/
theorem restrict_smul [∀ U : Cᵒᵖ, IsMulCommutative (R.obj.obj U)] (g : U' ⟶ U)
    (r : R.obj.obj (op U)) (f : GradedLocalHom M L n U) :
    (r • f).restrict g = R.obj.map g.op r • f.restrict g :=
  GradedLocalHom.ext fun i j hij V x => by
    rw [restrict_app, smul_app, smul_app, restrict_app]
    change (R.obj.map (g.op ≫ V.hom.op)) r • _ = _
    rw [Functor.map_comp]
    rfl

/-- Restriction along the identity is the identity. -/
theorem restrict_id (f : GradedLocalHom M L n U) : f.restrict (𝟙 U) = f :=
  GradedLocalHom.ext fun i j hij V x => by
    rw [restrict_app]
    exact f.app_mk_congr i j hij (Category.comp_id V.hom) x

/-- Restriction along a composite is the composite of the restrictions. -/
theorem restrict_comp (g : U' ⟶ U) (g' : U'' ⟶ U') (f : GradedLocalHom M L n U) :
    f.restrict (g' ≫ g) = (f.restrict g).restrict g' :=
  GradedLocalHom.ext fun i j hij V x => by
    rw [restrict_app, restrict_app, restrict_app]
    exact f.app_mk_congr i j hij (Category.assoc V.hom g' g).symm x

/-! ### Values over the slice site -/

/-- A local homomorphism is natural for the restriction from an object `V` of the slice site to
an object `W ⟶ V.left` mapping to it. -/
theorem map_app_eq (f : GradedLocalHom M L n U) (i j : ℤ) (hij : i + n = j) (V : Over U)
    {W : C} (g : W ⟶ V.left) (x : (M.piece i).val.obj (op V.left)) :
    (L.piece j).val.map g.op (f.app i j hij V x) =
      f.app i j hij (Over.mk (g ≫ V.hom)) ((M.piece i).val.map g.op x) :=
  f.naturality i j hij (V := V) (W := Over.mk (g ≫ V.hom)) (Over.homMk g) x

/-- The value of a local homomorphism over `W ⟶ U` is the value of its restriction to `W` over
the terminal object of the slice site. -/
theorem app_mk_eq_restrict (f : GradedLocalHom M L n U) (i j : ℤ) (hij : i + n = j) {W : C}
    (g : W ⟶ U) (y : (M.piece i).val.obj (op W)) :
    f.app i j hij (Over.mk g) y = (f.restrict g).app i j hij (Over.mk (𝟙 W)) y :=
  f.app_mk_congr i j hij (Category.id_comp g).symm y

/-- The member of a family `φ` indexed by a sieve at `f'` is the restriction of the member at
`f` along `g` when `g ≫ f = f'`. -/
private theorem family_eq_restrict {X : C} (S : Sieve X)
    (φ : ∀ ⦃W : C⦄ (f : W ⟶ X), S f → GradedLocalHom M L n W)
    (hφ : ∀ ⦃W W' : C⦄ (f : W ⟶ X) (g : W' ⟶ W) (hf : S f),
      φ (g ≫ f) (S.downward_closed hf g) = (φ f hf).restrict g)
    {W W' : C} {f : W ⟶ X} {f' : W' ⟶ X} (g : W' ⟶ W) (e : g ≫ f = f') (hf : S f)
    (hf' : S f') :
    φ f' hf' = (φ f hf).restrict g := by
  subst e
  exact hφ f g hf

/-! ### Gluing -/

/-- The presheaf of local sections of a sheaf of modules, as a presheaf of types, is a sheaf. -/
theorem sections_isSheafForget (F : SheafOfModules.{z} R) :
    Presieve.IsSheaf J (F.val.presheaf ⋙ CategoryTheory.forget AddCommGrpCat.{z}) :=
  (isSheaf_iff_isSheaf_of_type _ _).mp (Presheaf.isSheaf_comp_of_isSheaf _ _ _ F.isSheaf)

/-- Restriction along an identity is the identity, on local sections of a sheaf of modules. -/
theorem sections_map_id_apply (F : SheafOfModules.{w} R) {U : Cᵒᵖ} (x : F.val.obj U) :
    F.val.map (𝟙 U) x = x := by
  rw [F.val.map_id]; rfl

section Glue

variable {X : C} (S : Sieve X) (hS : S ∈ J X)
  (φ : ∀ ⦃W : C⦄ (f : W ⟶ X), S f → GradedLocalHom M L n W)
  (hφ : ∀ ⦃W W' : C⦄ (f : W ⟶ X) (g : W' ⟶ W) (hf : S f),
    φ (g ≫ f) (S.downward_closed hf g) = (φ f hf).restrict g)

/-- The family of local sections of `L` over the sieve `S` pulled back to `V`, whose gluing is
the value of the glued local homomorphism at a local section `x` of `M` over `V`. -/
noncomputable def glueFamily (i j : ℤ) (hij : i + n = j) (V : Over X)
    (x : (M.piece i).val.obj (op V.left)) :
    Presieve.FamilyOfElements ((L.piece j).val.presheaf ⋙ CategoryTheory.forget _)
      (S.pullback V.hom).arrows :=
  fun W g hg => (φ (g ≫ V.hom) hg).app i j hij (Over.mk (𝟙 W)) ((M.piece i).val.map g.op x)

include hφ in
/-- The family `SheafOfModules.GradedLocalHom.glueFamily` is compatible. -/
theorem glueFamily_compatible (i j : ℤ) (hij : i + n = j) (V : Over X)
    (x : (M.piece i).val.obj (op V.left)) :
    (glueFamily S φ i j hij V x).Compatible := by
  rw [Presieve.compatible_iff_sieveCompatible]
  intro W W' g h hg
  change (φ ((h ≫ g) ≫ V.hom) ((S.pullback V.hom).downward_closed hg h)).app i j hij
      (Over.mk (𝟙 W')) ((M.piece i).val.map (h ≫ g).op x) =
    (L.piece j).val.map h.op ((φ (g ≫ V.hom) hg).app i j hij (Over.mk (𝟙 W))
      ((M.piece i).val.map g.op x))
  rw [family_eq_restrict S φ hφ h (Category.assoc h g V.hom).symm hg
    ((S.pullback V.hom).downward_closed hg h)]
  refine Eq.trans ?_ (map_app_eq (φ (g ≫ V.hom) hg) i j hij (Over.mk (𝟙 W)) h _).symm
  have e2 : (M.piece i).val.map (h ≫ g).op x =
      (M.piece i).val.map h.op ((M.piece i).val.map g.op x) := by
    rw [op_comp, PresheafOfModules.map_comp_apply]
  change (φ (g ≫ V.hom) hg).app i j hij (Over.mk (𝟙 W' ≫ h))
      ((M.piece i).val.map (h ≫ g).op x) = _
  rw [e2]
  exact GradedLocalHom.app_mk_congr _ i j hij
    ((Category.id_comp h).trans (Category.comp_id h).symm) _

/-- The value of the glued local homomorphism at a local section `x` of `M` over `V`. -/
noncomputable def glueApp (i j : ℤ) (hij : i + n = j) (V : Over X)
    (x : (M.piece i).val.obj (op V.left)) : (L.piece j).val.obj (op V.left) :=
  (sections_isSheafForget (L.piece j) _ (J.pullback_stable V.hom hS)).amalgamate
    (glueFamily S φ i j hij V x) (glueFamily_compatible S φ hφ i j hij V x)

/-- The restriction of `SheafOfModules.GradedLocalHom.glueApp` along `g : W ⟶ V.left` with
`g ≫ V.hom` in `S` is the value of the member of the family at `g ≫ V.hom`. -/
theorem map_glueApp (i j : ℤ) (hij : i + n = j) (V : Over X)
    (x : (M.piece i).val.obj (op V.left)) {W : C} (g : W ⟶ V.left) (hg : S (g ≫ V.hom)) :
    (L.piece j).val.map g.op (glueApp S hS φ hφ i j hij V x) =
      (φ (g ≫ V.hom) hg).app i j hij (Over.mk (𝟙 W)) ((M.piece i).val.map g.op x) :=
  (sections_isSheafForget (L.piece j) _ (J.pullback_stable V.hom hS)).valid_glue
    (glueFamily_compatible S φ hφ i j hij V x) g hg

include hS in
/-- Two local sections of `L` over `V` agreeing after restriction to every member of the
pullback of the covering sieve `S` are equal. -/
theorem glue_ext (j : ℤ) (V : Over X) {y y' : (L.piece j).val.obj (op V.left)}
    (h : ∀ ⦃W : C⦄ (g : W ⟶ V.left), S (g ≫ V.hom) →
      (L.piece j).val.map g.op y = (L.piece j).val.map g.op y') :
    y = y' :=
  (sections_isSheafForget (L.piece j) _ (J.pullback_stable V.hom hS)).isSeparatedFor.ext
    fun _ g hg => h g hg

/-- The local homomorphism glued from a compatible family over a covering sieve. -/
noncomputable def glue : GradedLocalHom M L n X where
  app i j hij V := AddMonoidHom.mk' (glueApp S hS φ hφ i j hij V) (fun x y =>
    glue_ext S hS j V fun W g hg => by
      rw [map_add, map_glueApp S hS φ hφ i j hij V _ g hg,
        map_glueApp S hS φ hφ i j hij V _ g hg, map_glueApp S hS φ hφ i j hij V _ g hg,
        map_add]
      exact ((φ (g ≫ V.hom) hg).app i j hij (Over.mk (𝟙 W))).map_add _ _)
  map_smul i j hij V r x := glue_ext S hS j V fun W g hg => by
    change (L.piece j).val.map g.op (glueApp S hS φ hφ i j hij V (r • x)) =
      (L.piece j).val.map g.op (r • glueApp S hS φ hφ i j hij V x)
    rw [map_glueApp S hS φ hφ i j hij V _ g hg, PresheafOfModules.map_smul,
      PresheafOfModules.map_smul, map_glueApp S hS φ hφ i j hij V _ g hg]
    exact (φ (g ≫ V.hom) hg).map_smul i j hij (Over.mk (𝟙 W)) _ _
  naturality i j hij V W q x := glue_ext S hS j W fun W' g hg => by
    have hg' : S ((g ≫ q.left) ≫ V.hom) := by
      rw [Category.assoc, Over.w q]; exact hg
    change (L.piece j).val.map g.op ((L.piece j).val.map q.left.op
        (glueApp S hS φ hφ i j hij V x)) =
      (L.piece j).val.map g.op (glueApp S hS φ hφ i j hij W
        ((M.piece i).val.map q.left.op x))
    have e : φ ((g ≫ q.left) ≫ V.hom) hg' = φ (g ≫ W.hom) hg :=
      (fun {f f' : W' ⟶ X} (e : f = f') (hf : S f) (hf' : S f') => by subst e; rfl :
        ∀ {f f' : W' ⟶ X} (_ : f = f') (hf : S f) (hf' : S f'), φ f hf = φ f' hf')
        (by rw [Category.assoc, Over.w q]) hg' hg
    rw [← PresheafOfModules.map_comp_apply, ← op_comp, map_glueApp S hS φ hφ i j hij V x _ hg']
    refine Eq.trans ?_ (map_glueApp S hS φ hφ i j hij W _ g hg).symm
    rw [e, op_comp, PresheafOfModules.map_comp_apply]
  map_mul i j hij p V x b := glue_ext S hS (j + p) V fun W g hg => by
    change (L.piece (j + p)).val.map g.op (glueApp S hS φ hφ (i + p) (j + p) (by omega) V
        (M.smul i p (op V.left) x b)) =
      (L.piece (j + p)).val.map g.op
        (L.smul j p (op V.left) (glueApp S hS φ hφ i j hij V x) b)
    rw [map_glueApp S hS φ hφ (i + p) (j + p) (by omega) V _ g hg, M.smul_naturality,
      L.smul_naturality, map_glueApp S hS φ hφ i j hij V _ g hg]
    exact (φ (g ≫ V.hom) hg).map_mul i j hij p (Over.mk (𝟙 W)) _ _

/-- The value of the glued local homomorphism is `SheafOfModules.GradedLocalHom.glueApp`. -/
theorem glue_app (i j : ℤ) (hij : i + n = j) (V : Over X)
    (x : (M.piece i).val.obj (op V.left)) :
    (glue S hS φ hφ).app i j hij V x = glueApp S hS φ hφ i j hij V x := rfl

/-- A local homomorphism restricting to the members of the family is the glued one. -/
theorem eq_glue (f : GradedLocalHom M L n X)
    (hf : ∀ ⦃W : C⦄ (g : W ⟶ X) (hg : S g), f.restrict g = φ g hg) :
    f = glue S hS φ hφ :=
  GradedLocalHom.ext fun i j hij V x => glue_ext S hS j V fun W g hg => by
    refine (map_app_eq f i j hij V g x).trans (Eq.trans ?_
      (map_glueApp S hS φ hφ i j hij V x g hg).symm)
    refine (app_mk_eq_restrict f i j hij (g ≫ V.hom) _).trans ?_
    rw [hf _ hg]

end Glue

end GradedLocalHom

variable [∀ U : Cᵒᵖ, IsMulCommutative (R.obj.obj U)]

/-- The presheaf of `R`-modules `U ↦ SheafHom^n_A(M, L)(U)` of degree-`n` local
homomorphisms. -/
noncomputable abbrev gradedLocalHomPresheaf (M : GradedModule.{t, a, w} A)
    (L : GradedModule.{t, a, z} A) (n : ℤ) : PresheafOfModules.{max u v w z} R.obj where
  obj U := ModuleCat.of (R.obj.obj (op U.unop)) (GradedLocalHom M L n U.unop)
  map {U U'} g := ModuleCat.ofHom
      (Y := (ModuleCat.restrictScalars (R.obj.map g).hom).obj
        (ModuleCat.of (R.obj.obj (op U'.unop)) (GradedLocalHom M L n U'.unop)))
    { toFun := fun f => f.restrict g.unop
      map_add' := fun f f' => GradedLocalHom.restrict_add g.unop f f'
      map_smul' := fun r f => GradedLocalHom.restrict_smul g.unop r f }
  map_id U := by
    ext f
    exact GradedLocalHom.restrict_id f
  map_comp g g' := by
    ext f
    exact GradedLocalHom.restrict_comp g.unop g'.unop f

/-- The restriction map of `SheafOfModules.gradedLocalHomPresheaf` is restriction of local
homomorphisms. -/
theorem gradedLocalHomPresheaf_map_apply (M : GradedModule.{t, a, w} A)
    (L : GradedModule.{t, a, z} A) (n : ℤ) {U U' : Cᵒᵖ} (g : U ⟶ U')
    (f : GradedLocalHom M L n U.unop) :
    (gradedLocalHomPresheaf M L n).map g f = f.restrict g.unop := rfl

/-- **The degree-`n` local homomorphisms form a sheaf**: the presheaf
`U ↦ SheafHom^n_A(M, L)(U)` satisfies the sheaf condition. -/
theorem gradedLocalHomPresheaf_isSheaf (M : GradedModule.{t, a, w} A)
    (L : GradedModule.{t, a, z} A) (n : ℤ) :
    Presheaf.IsSheaf J (gradedLocalHomPresheaf M L n).presheaf := by
  refine Presheaf.isSheaf_of_isSheaf_comp J _
    (CategoryTheory.forget AddCommGrpCat.{max u v w z}) ?_
  rw [isSheaf_iff_isSheaf_of_type]
  intro X S hS x hx
  let φ : ∀ ⦃W : C⦄ (f : W ⟶ X), S f → GradedLocalHom M L n W := fun W f hf => x f hf
  have hφ : ∀ ⦃W W' : C⦄ (f : W ⟶ X) (g : W' ⟶ W) (hf : S f),
      φ (g ≫ f) (S.downward_closed hf g) = (φ f hf).restrict g :=
    fun W W' f g hf => hx.to_sieveCompatible f g hf
  have hr : ∀ ⦃W : C⦄ (f : W ⟶ X) (hf : S f),
      (GradedLocalHom.glue S hS φ hφ).restrict f = φ f hf :=
    fun W f hf => GradedLocalHom.ext fun i j hij V y => by
      rw [GradedLocalHom.restrict_app, GradedLocalHom.glue_app]
      have hm : S (𝟙 V.left ≫ (Over.mk (V.hom ≫ f)).hom) := by
        rw [Category.id_comp]; exact S.downward_closed hf V.hom
      have h := GradedLocalHom.map_glueApp S hS φ hφ i j hij (Over.mk (V.hom ≫ f)) y
        (𝟙 V.left) hm
      rw [GradedLocalHom.family_eq_restrict S φ hφ (f' := 𝟙 V.left ≫ (Over.mk (V.hom ≫ f)).hom)
        V.hom (Category.id_comp _).symm hf hm] at h
      refine (GradedLocalHom.sections_map_id_apply _ _).symm.trans (h.trans ?_)
      refine (congrArg ((φ f hf).app i j hij (Over.mk (𝟙 V.left ≫ V.hom)))
        (GradedLocalHom.sections_map_id_apply (M.piece i) y)).trans ?_
      exact GradedLocalHom.app_mk_congr _ i j hij (Category.id_comp V.hom) y
  exact ⟨GradedLocalHom.glue S hS φ hφ, fun W f hf => hr f hf,
    fun t ht => GradedLocalHom.eq_glue S hS φ hφ t fun W g hg => ht g hg⟩

/-- **Stacks 0FR3, the degree-`n` term `SheafHom^n_A(M, L)`.** The sheaf of `R`-modules whose
sections over `U` are the degree-`n` local homomorphisms `M|_U → L|_U`: the families
`f = (f_i)` of `R|_U`-linear maps `f_i : M^i|_U → L^{i + n}|_U` with `f_{i + p}(x a) = f_i(x) a`
for local sections `a` of `A^p`. These are exactly the local sections of
`∏_i SheafHom_R(M^i, L^{i + n})` satisfying that condition, so this is the subsheaf of the
product described in the source. -/
@[stacks 0FR3 "the degree-`n` term `SheafHom^n_A(M, L)`, a subsheaf of
`∏ SheafHom_O(M^i, L^{i + n})`, as a sheaf of `O`-modules"]
noncomputable def gradedLocalHomSheaf (M : GradedModule.{t, a, w} A)
    (L : GradedModule.{t, a, z} A) (n : ℤ) : SheafOfModules.{max u v w z} R where
  val := gradedLocalHomPresheaf M L n
  isSheaf := gradedLocalHomPresheaf_isSheaf M L n

/-- The module of sections of `SheafOfModules.gradedLocalHomSheaf` over `U` is the module of
degree-`n` local homomorphisms over `U`. -/
theorem gradedLocalHomSheaf_obj (M : GradedModule.{t, a, w} A) (L : GradedModule.{t, a, z} A)
    (n : ℤ) (U : C) :
    (gradedLocalHomSheaf M L n).val.obj (op U) =
      ModuleCat.of (R.obj.obj (op U)) (GradedLocalHom M L n U) :=
  rfl

/-- **Stacks 0FR3, the graded `O`-module `SheafHom^gr_A(M, L)`.** The internal hom of two right
graded `A`-modules, as a graded sheaf of `R`-modules: in degree `n` the sheaf
`SheafOfModules.gradedLocalHomSheaf M L n` of degree-`n` local homomorphisms. -/
@[stacks 0FR3 "the graded `O`-module `SheafHom^gr_A(M, L)`"]
noncomputable abbrev gradedSheafHom (M : GradedModule.{t, a, w} A)
    (L : GradedModule.{t, a, z} A) : ℤ → SheafOfModules.{max u v w z} R :=
  gradedLocalHomSheaf M L

/-- **The constructed graded sheaf is the internal hom**: its sections are the local
homomorphisms, additively, `R`-linearly and compatibly with restriction. -/
noncomputable def isGradedSheafHom_gradedSheafHom (M : GradedModule.{t, a, w} A)
    (L : GradedModule.{t, a, z} A) : IsGradedSheafHom M L (gradedSheafHom M L) where
  sectionsEquiv _ _ := Equiv.refl _
  sectionsEquiv_add _ _ _ _ _ _ _ _ _ := rfl
  sectionsEquiv_smul _ _ _ _ _ _ _ _ _ := rfl
  sectionsEquiv_naturality _ _ _ _ _ _ _ _ _ := rfl

end Construction

/-! ### Composition of local homomorphisms -/

section Composition

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  {A : GradedAlgebra.{t, a} R}

namespace GradedLocalHom

variable {K : GradedModule.{t, a, w} A} {L : GradedModule.{t, a, z} A}
  {M : GradedModule.{t, a, s} A} {m n : ℤ} {U : C}

/-- Two composites of local homomorphisms through intermediate degrees `k = k'` agree. -/
theorem app_app_congr (g : GradedLocalHom L M m U) (f : GradedLocalHom K L n U) {i k k' j : ℤ}
    (hk : i + n = k) (hk' : i + n = k') (hkj : k + m = j) (hkj' : k' + m = j) (V : Over U)
    (x : (K.piece i).val.obj (op V.left)) :
    g.app k j hkj V (f.app i k hk V x) = g.app k' j hkj' V (f.app i k' hk' V x) := by
  subst hk hk'
  rfl

/-- The composite `g ∘ f` of a local homomorphism `f` of degree `n` and a local homomorphism `g`
of degree `m`, a local homomorphism of degree `n + m`. -/
def comp (g : GradedLocalHom L M m U) (f : GradedLocalHom K L n U) :
    GradedLocalHom K M (n + m) U where
  app i j hij V := (g.app (i + n) j (by omega) V).comp (f.app i (i + n) rfl V)
  map_smul i j hij V r x :=
    (congrArg (g.app (i + n) j (by omega) V) (f.map_smul i (i + n) rfl V r x)).trans
      (g.map_smul (i + n) j (by omega) V r _)
  naturality i j hij {V W} q x :=
    (g.naturality (i + n) j (by omega) q _).trans
      (congrArg (g.app (i + n) j (by omega) W) (f.naturality i (i + n) rfl q x))
  map_mul i j hij p V x b :=
    (app_app_congr g f (i := i + p) rfl (show i + p + n = i + n + p by omega) (by omega)
        (by omega) V _).trans
      ((congrArg (g.app (i + n + p) (j + p) (by omega) V)
          (f.map_mul i (i + n) rfl p V x b)).trans
        (g.map_mul (i + n) j (by omega) p V _ b))

/-- The value of `g.comp f` is the value of `g` at the value of `f`. -/
theorem comp_app (g : GradedLocalHom L M m U) (f : GradedLocalHom K L n U) (i j : ℤ)
    (hij : i + (n + m) = j) (k : ℤ) (hk : i + n = k) (V : Over U)
    (x : (K.piece i).val.obj (op V.left)) :
    (g.comp f).app i j hij V x = g.app k j (by omega) V (f.app i k hk V x) := by
  subst hk
  rfl

/-- Composition is additive in the first variable. -/
theorem add_comp (g g' : GradedLocalHom L M m U) (f : GradedLocalHom K L n U) :
    (g + g').comp f = g.comp f + g'.comp f := rfl

/-- Composition is additive in the second variable. -/
theorem comp_add (g : GradedLocalHom L M m U) (f f' : GradedLocalHom K L n U) :
    g.comp (f + f') = g.comp f + g.comp f' :=
  GradedLocalHom.ext fun i j hij V x => map_add (g.app (i + n) j (by omega) V) _ _

/-- Restriction commutes with composition. -/
theorem restrict_comp' {U' : C} (h : U' ⟶ U) (g : GradedLocalHom L M m U)
    (f : GradedLocalHom K L n U) :
    (g.comp f).restrict h = (g.restrict h).comp (f.restrict h) := rfl

variable [∀ U : Cᵒᵖ, IsMulCommutative (R.obj.obj U)]

/-- Composition is linear in the first variable. -/
theorem smul_comp (r : R.obj.obj (op U)) (g : GradedLocalHom L M m U)
    (f : GradedLocalHom K L n U) : (r • g).comp f = r • g.comp f := rfl

/-- Composition is linear in the second variable. -/
theorem comp_smul (r : R.obj.obj (op U)) (g : GradedLocalHom L M m U)
    (f : GradedLocalHom K L n U) : g.comp (r • f) = r • g.comp f :=
  GradedLocalHom.ext fun i j hij V x => g.map_smul (i + n) j (by omega) V _ _

end GradedLocalHom

end Composition

/-! ### The composition map out of the tensor product -/

section CompositionMap

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} (O : Sheaf J CommRingCat.{t})

attribute [local instance high] Stacks.hasSheafCompose_forget₂_commRingCat

variable {A : GradedAlgebra.{t, a} (CategoryTheory.Sheaf.toRingCat J O)}
  {K L M : GradedModule.{t, a, w} A}

/-- `SheafHom^n_A(M, L)` as a presheaf of modules over the presheaf of commutative rings
underlying `O`, the form in which the objectwise tensor product of presheaves of modules takes
its factors. -/
noncomputable def gradedLocalHomPresheafOver (M L : GradedModule.{t, a, w} A) (n : ℤ) :
    PresheafOfModules.{max u v w} (O.obj ⋙ forget₂ CommRingCat RingCat) :=
  (gradedLocalHomSheaf M L n).val

/-- Composition of local homomorphisms, as a bilinear map of presheaves of modules
`SheafHom^m_A(L, M) × SheafHom^n_A(K, L) → SheafHom^{n + m}_A(K, M)`. -/
noncomputable def gradedSheafHomCompBilinear (m n : ℤ) :
    Stacks.BilinearMap (gradedLocalHomPresheafOver O L M m) (gradedLocalHomPresheafOver O K L n)
      (gradedLocalHomPresheafOver O K M (n + m)) where
  app X := AddMonoidHom.mk'
    (fun g => AddMonoidHom.mk' (fun f => GradedLocalHom.comp (U := X.unop) g f)
      (fun f f' => GradedLocalHom.comp_add (U := X.unop) g f f'))
    (fun g g' => AddMonoidHom.ext fun f => GradedLocalHom.add_comp (U := X.unop) g g' f)
  map_smul_left X r g f := GradedLocalHom.ext fun _ _ _ _ _ => rfl
  map_smul_right X r g f := GradedLocalHom.ext fun i j hij V x =>
    GradedLocalHom.map_smul (U := X.unop) g (i + n) j (by omega) V _ _
  naturality γ g f := GradedLocalHom.restrict_comp' γ.unop g f

/-- The bilinear composition map sends `(g, f)` to `g ∘ f`. -/
theorem gradedSheafHomCompBilinear_app (m n : ℤ) (X : Cᵒᵖ)
    (g : (gradedLocalHomPresheafOver O L M m).obj X)
    (f : (gradedLocalHomPresheafOver O K L n).obj X) :
    (gradedSheafHomCompBilinear O m n).app X g f = GradedLocalHom.comp (U := X.unop) g f := rfl

variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
  [HasWeakSheafify J AddCommGrpCat.{max u v w}]

variable (K L M) in
/-- The tensor product `SheafHom^m_A(L, M) ⊗_O SheafHom^n_A(K, L)` of sheaves of `O`-modules:
the sheafification of the objectwise tensor product of the underlying presheaves of modules,
which is the definition of the tensor product of sheaves of modules [Stacks, Tag 01CA]
(`Stacks.SheafOfModules.Tensor.sheafTensor`). -/
noncomputable abbrev gradedSheafHomTensor (m n : ℤ) :
    SheafOfModules.{max u v w} (CategoryTheory.Sheaf.toRingCat J O) :=
  (PresheafOfModules.sheafification (𝟙 (CategoryTheory.Sheaf.toRingCat J O).obj)).obj
    (PresheafOfModules.tensorObj (gradedLocalHomPresheafOver O L M m)
      (gradedLocalHomPresheafOver O K L n))

/-- **Stacks 0FR3, the composition map.** The morphism of sheaves of `O`-modules
`SheafHom^m_A(L, M) ⊗_O SheafHom^n_A(K, L) ⟶ SheafHom^{n + m}_A(K, M)` given locally by
composition, `g ⊗ f ↦ g ∘ f` (`SheafOfModules.gradedSheafHomComp_tmul`). -/
@[stacks 0FR3 "the composition map
`SheafHom^m_A(L, M) ⊗_O SheafHom^n_A(K, L) → SheafHom^{n + m}_A(K, M)`"]
noncomputable def gradedSheafHomComp (m n : ℤ) :
    gradedSheafHomTensor O K L M m n ⟶ gradedLocalHomSheaf K M (n + m) :=
  ((PresheafOfModules.sheafificationAdjunction
      (𝟙 (CategoryTheory.Sheaf.toRingCat J O).obj)).homEquiv
        (PresheafOfModules.tensorObj (gradedLocalHomPresheafOver O L M m)
          (gradedLocalHomPresheafOver O K L n)) (gradedLocalHomSheaf K M (n + m))).symm
    (PresheafOfModules.ofBilinear (gradedSheafHomCompBilinear O m n))

/-- The composition map sends the image of `g ⊗ f` in the tensor product to `g ∘ f`. -/
theorem gradedSheafHomComp_tmul (m n : ℤ) (X : Cᵒᵖ)
    (g : (gradedLocalHomPresheafOver O L M m).obj X)
    (f : (gradedLocalHomPresheafOver O K L n).obj X) :
    PresheafOfModules.Hom.app (gradedSheafHomComp O (K := K) (L := L) (M := M) m n).val X
        (PresheafOfModules.Hom.app ((PresheafOfModules.sheafificationAdjunction
          (𝟙 (CategoryTheory.Sheaf.toRingCat J O).obj)).unit.app
            (PresheafOfModules.tensorObj (gradedLocalHomPresheafOver O L M m)
              (gradedLocalHomPresheafOver O K L n))) X (g ⊗ₜ f)) =
      GradedLocalHom.comp (U := X.unop) g f :=
  (PresheafOfModules.hom_congr_apply
    (PresheafOfModules.sheafificationAdjunction_unit_comp_homEquiv_symm
      (𝟙 (CategoryTheory.Sheaf.toRingCat J O).obj) (N := gradedLocalHomSheaf K M (n + m))
      (PresheafOfModules.ofBilinear (gradedSheafHomCompBilinear O m n))) X (g ⊗ₜ f)).trans
    (PresheafOfModules.ofBilinear_tmul _ X g f)

/-- **Stacks 0FR3, the composition map of graded `O`-modules.** Degree `k` of the tensor product
of the graded `O`-modules `SheafHom^gr_A(L, M)` and `SheafHom^gr_A(K, L)` is
`⨁_{m + n = k} SheafHom^m_A(L, M) ⊗_O SheafHom^n_A(K, L)` (the tensor product of
[Stacks, Tag 0FR2] over the graded algebra `O`, concentrated in degree `0`), and the composition
map on it is `SheafOfModules.gradedSheafHomComp m n` on the summand of index `(m, n)`. -/
@[stacks 0FR3 "the composition map on degree `k` of
`SheafHom^gr_A(L, M) ⊗_O SheafHom^gr_A(K, L)`"]
noncomputable def gradedSheafHomCompSum (k : ℤ) :
    (∐ fun p : {p : ℤ × ℤ // p.1 + p.2 = k} =>
      gradedSheafHomTensor O K L M p.1.1 p.1.2) ⟶ gradedLocalHomSheaf K M k :=
  Sigma.desc fun p => gradedSheafHomComp O p.1.1 p.1.2 ≫
    eqToHom (congrArg (gradedLocalHomSheaf K M) (by have := p.2; omega))

/-- On the summand of index `(m, n)`, the graded composition map is
`SheafOfModules.gradedSheafHomComp m n`. -/
theorem ι_gradedSheafHomCompSum (k : ℤ) (p : {p : ℤ × ℤ // p.1 + p.2 = k}) :
    Sigma.ι (fun p : {p : ℤ × ℤ // p.1 + p.2 = k} =>
        gradedSheafHomTensor O K L M p.1.1 p.1.2) p ≫ gradedSheafHomCompSum O k =
      gradedSheafHomComp O p.1.1 p.1.2 ≫
        eqToHom (congrArg (gradedLocalHomSheaf K M) (by have := p.2; omega)) :=
  Sigma.ι_desc _ _

end CompositionMap

/-! ### Global sections -/

section GlobalSections

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  {A : GradedAlgebra.{t, a} R}

namespace GradedHomOfDegree

variable {K L M : GradedModule.{t, a, w} A} {m n : ℤ}

/-- **Composition in the graded category `Mod^gr(A)` of Stacks 0FR1**: the composite
`g ∘ f : K → M`, homogeneous of degree `n + m`, of homogeneous homomorphisms `f : K → L` of
degree `n` and `g : L → M` of degree `m`. -/
@[stacks 0FR1 "composition `Hom^m(L, M) × Hom^n(K, L) → Hom^{n + m}(K, M)` in `Mod^gr(A)`"]
def comp (g : GradedHomOfDegree L M m) (f : GradedHomOfDegree K L n) :
    GradedHomOfDegree K M (n + m) :=
  ofLocal (fun U => (g.toLocal U).comp (f.toLocal U)) (by intros; rfl)

/-- The restriction of a composite to a slice site is the composite of the restrictions. -/
theorem toLocal_comp (g : GradedHomOfDegree L M m) (f : GradedHomOfDegree K L n) (U : C) :
    (g.comp f).toLocal U = (g.toLocal U).comp (f.toLocal U) :=
  toLocal_ofLocal _ (by intros; rfl) U

/-- The components of a composite are the composites of the components: `g.comp f` is simple
composition of right graded module maps. -/
theorem comp_app (g : GradedHomOfDegree L M m) (f : GradedHomOfDegree K L n) (i j : ℤ)
    (hij : i + (n + m) = j) :
    (g.comp f).app i j hij = f.app i (i + n) rfl ≫ g.app (i + n) j (by omega) :=
  SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun _ =>
    ModuleCat.hom_ext (LinearMap.ext fun _ => rfl))

variable [∀ U : Cᵒᵖ, IsMulCommutative (R.obj.obj U)]

/-- The global section of `SheafHom^n_A(M, L)` given by a homogeneous homomorphism of degree
`n`: its restrictions to the slice sites. -/
def toSections (f : GradedHomOfDegree M L n) : (gradedLocalHomSheaf M L n).sections :=
  ⟨fun U => f.toLocal U.unop, fun γ => f.restrict_toLocal γ.unop⟩

/-- The homogeneous homomorphism of degree `n` assembled from a global section of
`SheafHom^n_A(M, L)`. -/
def ofSections (s : (gradedLocalHomSheaf M L n).sections) : GradedHomOfDegree M L n :=
  ofLocal (fun U => s.1 (op U)) (fun g => s.2 g.op)

/-- A homogeneous homomorphism is determined by the global section it defines. -/
theorem toSections_injective : Function.Injective (toSections (M := M) (L := L) (n := n)) :=
  fun _ _ h => eq_of_toLocal fun U => congrArg (fun s => s.1 (op U)) h

/-- The zero homomorphism of degree `n`. -/
instance : Zero (GradedHomOfDegree M L n) := ⟨ofLocal (fun _ => 0) (by intros; rfl)⟩

/-- The sum of two homomorphisms of degree `n`. -/
instance : Add (GradedHomOfDegree M L n) :=
  ⟨fun f g => ofLocal (fun U => f.toLocal U + g.toLocal U) (by intros; rfl)⟩

/-- The negation of a homomorphism of degree `n`. -/
instance : Neg (GradedHomOfDegree M L n) :=
  ⟨fun f => ofLocal (fun U => -f.toLocal U) (by intros; rfl)⟩

/-- The difference of two homomorphisms of degree `n`. -/
instance : Sub (GradedHomOfDegree M L n) :=
  ⟨fun f g => ofLocal (fun U => f.toLocal U - g.toLocal U) (by intros; rfl)⟩

/-- The multiple of a homomorphism of degree `n` by a natural number. -/
instance : SMul ℕ (GradedHomOfDegree M L n) :=
  ⟨fun k f => ofLocal (fun U => k • f.toLocal U) (by intros; rfl)⟩

/-- The multiple of a homomorphism of degree `n` by an integer. -/
instance : SMul ℤ (GradedHomOfDegree M L n) :=
  ⟨fun k f => ofLocal (fun U => k • f.toLocal U) (by intros; rfl)⟩

/-- Multiplying the restrictions of a homogeneous homomorphism by a global section of `R` gives
a compatible family of local homomorphisms. -/
theorem smul_toLocal_restrict (a : Stacks.Cohomology.SiteModules.GlobalSectionRing R)
    (f : GradedHomOfDegree M L n) {U U' : C} (g : U' ⟶ U) :
    (a.1 (op U) • f.toLocal U).restrict g = a.1 (op U') • f.toLocal U' :=
  (GradedLocalHom.restrict_smul g _ _).trans (by
    rw [f.restrict_toLocal g]
    exact congrArg (fun r => r • f.toLocal U') (a.2 g.op))

/-- The multiple of a homomorphism of degree `n` by a global section `a` of `R`: on sections over
`U` it is multiplication by `a|_U` after the homomorphism. -/
instance : SMul (Stacks.Cohomology.SiteModules.GlobalSectionRing R)
    (GradedHomOfDegree M L n) :=
  ⟨fun a f => ofLocal (fun U => a.1 (op U) • f.toLocal U) (smul_toLocal_restrict a f)⟩

/-- The global section of the zero homomorphism is zero. -/
theorem toSections_zero : toSections (0 : GradedHomOfDegree M L n) = 0 :=
  Subtype.ext (funext fun (U : Cᵒᵖ) => toLocal_ofLocal _ (by intros; rfl) U.unop)

/-- Taking global sections is additive. -/
theorem toSections_add (f g : GradedHomOfDegree M L n) :
    toSections (f + g) = toSections f + toSections g :=
  Subtype.ext (funext fun (U : Cᵒᵖ) => toLocal_ofLocal _ (by intros; rfl) U.unop)

/-- Taking global sections commutes with negation. -/
theorem toSections_neg (f : GradedHomOfDegree M L n) : toSections (-f) = -toSections f :=
  Subtype.ext (funext fun (U : Cᵒᵖ) => toLocal_ofLocal _ (by intros; rfl) U.unop)

/-- Taking global sections commutes with subtraction. -/
theorem toSections_sub (f g : GradedHomOfDegree M L n) :
    toSections (f - g) = toSections f - toSections g :=
  Subtype.ext (funext fun (U : Cᵒᵖ) => toLocal_ofLocal _ (by intros; rfl) U.unop)

/-- Taking global sections commutes with multiplication by a natural number. -/
theorem toSections_nsmul (f : GradedHomOfDegree M L n) (k : ℕ) :
    toSections (k • f) = k • toSections f :=
  Subtype.ext (funext fun (U : Cᵒᵖ) => toLocal_ofLocal _ (by intros; rfl) U.unop)

/-- Taking global sections commutes with multiplication by an integer. -/
theorem toSections_zsmul (f : GradedHomOfDegree M L n) (k : ℤ) :
    toSections (k • f) = k • toSections f :=
  Subtype.ext (funext fun (U : Cᵒᵖ) => toLocal_ofLocal _ (by intros; rfl) U.unop)

/-- Taking global sections is linear over the global sections of `R`. -/
theorem toSections_smul (a : Stacks.Cohomology.SiteModules.GlobalSectionRing R)
    (f : GradedHomOfDegree M L n) : toSections (a • f) = a • toSections f :=
  Subtype.ext (funext fun (U : Cᵒᵖ) => toLocal_ofLocal _ (smul_toLocal_restrict a f) U.unop)

/-- The homomorphisms of degree `n` form an additive group under pointwise operations. -/
noncomputable instance : AddCommGroup (GradedHomOfDegree M L n) :=
  Function.Injective.addCommGroup toSections toSections_injective toSections_zero toSections_add
    toSections_neg toSections_sub toSections_nsmul toSections_zsmul

/-- The homomorphisms of degree `n` form a module over the ring `Γ(C, R)` of global sections. -/
noncomputable instance : Module (Stacks.Cohomology.SiteModules.GlobalSectionRing R)
    (GradedHomOfDegree M L n) :=
  Function.Injective.module _ ⟨⟨toSections, toSections_zero⟩, toSections_add⟩
    toSections_injective toSections_smul

omit [∀ U : Cᵒᵖ, IsMulCommutative (R.obj.obj U)] in
/-- The components of a sum are the sums of the components. -/
theorem add_app (f g : GradedHomOfDegree M L n) (i j : ℤ) (hij : i + n = j) :
    (f + g).app i j hij = f.app i j hij + g.app i j hij :=
  SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun _ =>
    ModuleCat.hom_ext (LinearMap.ext fun _ => rfl))

/-- The components of `a • f` are multiplication by `a` after the components of `f`. -/
theorem smul_app_apply (a : Stacks.Cohomology.SiteModules.GlobalSectionRing R)
    (f : GradedHomOfDegree M L n) (i j : ℤ) (hij : i + n = j) (U : Cᵒᵖ)
    (x : (M.piece i).val.obj U) :
    ((a • f).app i j hij).val.app U x = a.1 U • (f.app i j hij).val.app U x :=
  congrArg (· • (f.app i j hij).val.app U x) (ring_map_top U.unop (a.1 (op U.unop)))

end GradedHomOfDegree

variable [∀ U : Cᵒᵖ, IsMulCommutative (R.obj.obj U)]

/-- **Stacks 0FR3, `Hom_{Mod^gr(A)}(M, L) = Γ(C, SheafHom^gr_A(M, L))`.** In each degree `n`,
the homomorphisms `M → L` of right graded `A`-modules homogeneous of degree `n` are the global
sections of `SheafHom^n_A(M, L)`, as modules over the ring `Γ(C, R)` of global sections: a
homomorphism is sent to the compatible family of its restrictions to the slice sites. Its
compatibility with composition is `SheafOfModules.gradedHomLinearEquivSections_comp`. -/
@[stacks 0FR3 "`Hom_{Mod^gr(A)}(M, L) = Γ(C, SheafHom^gr_A(M, L))` as graded `Γ(C, O)`-modules,
degreewise"]
noncomputable def gradedHomLinearEquivSections (M L : GradedModule.{t, a, w} A) (n : ℤ) :
    GradedHomOfDegree M L n ≃ₗ[Stacks.Cohomology.SiteModules.GlobalSectionRing R]
      Stacks.Cohomology.SiteModules.GlobalSections R (gradedLocalHomSheaf M L n) where
  toFun := GradedHomOfDegree.toSections
  map_add' := GradedHomOfDegree.toSections_add
  map_smul' := GradedHomOfDegree.toSections_smul
  invFun := GradedHomOfDegree.ofSections
  left_inv f := GradedHomOfDegree.eq_of_toLocal fun U =>
    GradedHomOfDegree.toLocal_ofLocal (fun U => f.toLocal U) (fun g => f.restrict_toLocal g) U
  right_inv s := Subtype.ext (funext fun (U : Cᵒᵖ) =>
    GradedHomOfDegree.toLocal_ofLocal (fun U => s.1 (op U)) (fun g => s.2 g.op) U.unop)

/-- The global section of `SheafHom^n_A(M, L)` attached to `f` has value `f|_U` over `U`. -/
theorem gradedHomLinearEquivSections_apply (M L : GradedModule.{t, a, w} A) (n : ℤ)
    (f : GradedHomOfDegree M L n) (U : Cᵒᵖ) :
    (gradedHomLinearEquivSections M L n f).1 U = f.toLocal U.unop := rfl

/-- The identification of `Hom^gr` with global sections takes composition of homomorphisms to
composition of local homomorphisms. -/
theorem gradedHomLinearEquivSections_comp_local {K L M : GradedModule.{t, a, w} A} {m n : ℤ}
    (g : GradedHomOfDegree L M m) (f : GradedHomOfDegree K L n) (U : Cᵒᵖ) :
    (gradedHomLinearEquivSections K M (n + m) (g.comp f)).1 U =
      ((gradedHomLinearEquivSections L M m g).1 U).comp
        ((gradedHomLinearEquivSections K L n f).1 U) :=
  GradedHomOfDegree.toLocal_comp g f U.unop

end GlobalSections

/-! ### Compatibility with composition -/

section CompositionCompatibility

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} (O : Sheaf J CommRingCat.{t})

attribute [local instance high] Stacks.hasSheafCompose_forget₂_commRingCat

variable {A : GradedAlgebra.{t, a} (CategoryTheory.Sheaf.toRingCat J O)}
  {K L M : GradedModule.{t, a, w} A}
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
  [HasWeakSheafify J AddCommGrpCat.{max u v w}]

/-- **Stacks 0FR3, compatibility with composition.** Under
`Hom_{Mod^gr(A)}(-, -) = Γ(C, SheafHom^gr_A(-, -))`, composition `g ∘ f` of homogeneous
homomorphisms corresponds to the composition map
`SheafHom^m_A(L, M) ⊗_O SheafHom^n_A(K, L) → SheafHom^{n + m}_A(K, M)` applied to the image of
the section `g ⊗ f` of the tensor product, over every object. -/
@[stacks 0FR3 "the identification with global sections is compatible with composition"]
theorem gradedHomLinearEquivSections_comp {m n : ℤ} (g : GradedHomOfDegree L M m)
    (f : GradedHomOfDegree K L n) (X : Cᵒᵖ) :
    (gradedHomLinearEquivSections K M (n + m) (g.comp f)).1 X =
      PresheafOfModules.Hom.app (gradedSheafHomComp O (K := K) (L := L) (M := M) m n).val X
        (PresheafOfModules.Hom.app ((PresheafOfModules.sheafificationAdjunction
          (𝟙 (CategoryTheory.Sheaf.toRingCat J O).obj)).unit.app
            (PresheafOfModules.tensorObj (gradedLocalHomPresheafOver O L M m)
              (gradedLocalHomPresheafOver O K L n))) X
          ((show (gradedLocalHomPresheafOver O L M m).obj X from
              (gradedHomLinearEquivSections L M m g).1 X) ⊗ₜ
            (show (gradedLocalHomPresheafOver O K L n).obj X from
              (gradedHomLinearEquivSections K L n f).1 X))) :=
  (gradedHomLinearEquivSections_comp_local g f X).trans
    (gradedSheafHomComp_tmul O m n X _ _).symm

end CompositionCompatibility

end SheafOfModules

end
