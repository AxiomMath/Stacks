module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedExtensionByZero
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedTensorHomAdjunction

/-!
# Functoriality of the tensor-hom adjunction for sheaves of graded modules

Let `R` be a sheaf of rings on a site `(C, J)`, let `A` and `B` be sheaves of graded
`R`-algebras, let `M` be a right graded `A`-module, let `N` be a graded `(A, B)`-bimodule and
let `L` be a right graded `B`-module. The two identities

`Hom_{Mod^gr(B)}(M ⊗_A N, L) = Hom_{Mod^gr(A)}(M, SheafHom^gr_B(N, L))`

and

`SheafHom^gr_B(M ⊗_A N, L) = SheafHom^gr_A(M, SheafHom^gr_B(N, L))`

of `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/GradedTensorHomAdjunction.lean` hold
functorially in `M`, `N` and `L`. This file constructs the morphisms which morphisms of `M`, `N`
and `L` induce between tensor products and between internal homs, and proves that both
identities are natural in each of the three variables.

## Main definitions

* `SheafOfModules.GradedLocalHom.precompPostcomp` composes a local homomorphism `M|_U → L|_U`
  with morphisms `M' ⟶ M` and `L ⟶ L'` of right graded modules.
* `SheafOfModules.IsGradedSheafHom.map` is the morphism `SheafHom^gr(M, L) ⟶ SheafHom^gr(M', L')`
  of graded sheaves of `R`-modules induced by `M' ⟶ M` and `L ⟶ L'`.
* `SheafOfModules.IsGradedInternalHom.map` is the morphism
  `SheafHom^gr_B(N, L) ⟶ SheafHom^gr_B(N', L')` of right graded `A`-modules induced by a morphism
  `N' ⟶ N` of graded bimodules and a morphism `L ⟶ L'` of right graded `B`-modules.
* `SheafOfModules.IsGradedTensorProduct.map` is the morphism `M ⊗_A N ⟶ M' ⊗_A N'` of right
  graded `B`-modules induced by `M ⟶ M'` and `N ⟶ N'`; it sends `x ⊗ y` to `u x ⊗ σ y`
  (`SheafOfModules.IsGradedTensorProduct.map_tmul`).

## Main results

* `SheafOfModules.tensorHomEquiv_naturality_left`, `tensorHomEquiv_naturality_bimodule` and
  `tensorHomEquiv_naturality_right`: the first identity `SheafOfModules.tensorHomEquiv` is
  natural in `M`, in `N` and in `L`.
* `SheafOfModules.isGradedSheafHom_tensor_map_left`, `isGradedSheafHom_tensor_map_bimodule` and
  `isGradedSheafHom_tensor_map_right`: under the second identity
  `SheafOfModules.isGradedSheafHom_tensor`, the morphism of internal homs induced by a morphism
  of `M`, of `N` or of `L` on the side `SheafHom^gr_B(M ⊗_A N, L)` is the morphism induced on the
  side `SheafHom^gr_A(M, SheafHom^gr_B(N, L))`.

## Implementation notes

The second identity is an equality of objects (a graded sheaf which is the one internal hom is
also the other), so its functoriality says that the two descriptions of a graded sheaf induce
the same morphisms: for each morphism of `M`, `N` or `L`, the morphism of graded sheaves of
`R`-modules induced through `SheafHom^gr_B(M ⊗_A N, L)` equals the one induced through
`SheafHom^gr_A(M, SheafHom^gr_B(N, L))`. The first identity is an equivalence of types, and its
functoriality is the usual commutation with precomposition and postcomposition
(`SheafOfModules.GradedHomOfDegree.compLeft` and `compRight`).

The induced morphisms are built from the universal properties: a morphism of internal homs from
the identification of local sections with local homomorphisms, and a morphism of tensor products
from the universal property of the tensor product applied to `(x, y) ↦ u x ⊗ σ y`.

## References

* [Stacks Project, Tag 0FR6](https://stacks.math.columbia.edu/tag/0FR6)
-/

@[expose] public section

open CategoryTheory

universe t a w z s g v u

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  {A B : GradedAlgebra.{t, a} R}

/-- Two homogeneous homomorphisms of degree `n` agree when their components agree on the sections
over every object of the site. -/
theorem GradedHomOfDegree.ext_sections {M L : GradedModule.{t, a, w} A} {n : ℤ}
    {f g : GradedHomOfDegree M L n}
    (h : ∀ (i j : ℤ) (hij : i + n = j) (U : C) (x : (M.piece i).val.obj (Opposite.op U)),
      (f.app i j hij).val.app (Opposite.op U) x = (g.app i j hij).val.app (Opposite.op U) x) :
    f = g :=
  GradedHomOfDegree.ext fun i j hij => SheafOfModules.hom_ext (PresheafOfModules.hom_ext
    fun U => ModuleCat.hom_ext (LinearMap.ext fun x => h i j hij U.unop x))

/-- A homogeneous homomorphism of degree zero is a morphism of right graded modules. -/
def GradedHomOfDegree.toHom {M L : GradedModule.{t, a, w} A} (f : GradedHomOfDegree M L 0) :
    M ⟶ L where
  app i := f.app i i (add_zero i)
  map_smul n i U x y := f.map_mul n n (add_zero n) i U x y

/-- The components of `f.toHom` are the components of `f`. -/
@[simp]
theorem GradedHomOfDegree.toHom_app {M L : GradedModule.{t, a, w} A}
    (f : GradedHomOfDegree M L 0) (i : ℤ) : f.toHom.app i = f.app i i (add_zero i) := rfl

/-- A morphism of graded bimodules is a morphism of the underlying right graded modules. -/
def GradedBimodule.Hom.toGradedModuleHom {N N' : GradedBimodule.{t, a, z} A B} (σ : N ⟶ N') :
    N.toGradedModule ⟶ N'.toGradedModule where
  app n := σ.app n
  map_smul n i U x y := σ.map_rightMul n i U x y

/-- The components of `σ.toGradedModuleHom` are the components of `σ`. -/
@[simp]
theorem GradedBimodule.Hom.toGradedModuleHom_app {N N' : GradedBimodule.{t, a, z} A B}
    (σ : N ⟶ N') (n : ℤ) : (GradedBimodule.Hom.toGradedModuleHom σ).app n = σ.app n := rfl

/-! ### Composing local homomorphisms with morphisms of graded modules -/

section LocalComposition

variable {M M' : GradedModule.{t, a, w} A} {L L' : GradedModule.{t, a, z} A}

/-- The composite `M'|_U → M|_U → L|_U → L'|_U` of a degree-`n` local homomorphism
`f : M|_U → L|_U` with morphisms `u : M' ⟶ M` and `k : L ⟶ L'` of right graded modules. -/
def GradedLocalHom.precompPostcomp (u : M' ⟶ M) (k : L ⟶ L') {n : ℤ} {U : C}
    (f : GradedLocalHom M L n U) : GradedLocalHom M' L' n U where
  app i j hij V := (homSections (k.app j) (Opposite.op V.left)).comp
    ((f.app i j hij V).comp (homSections (u.app i) (Opposite.op V.left)))
  map_smul i j hij V r x := by
    change homSections (k.app j) _ (f.app i j hij V (homSections (u.app i) _ (r • x))) =
      r • homSections (k.app j) _ (f.app i j hij V (homSections (u.app i) _ x))
    rw [homSections_smul, f.map_smul, homSections_smul]
  naturality i j hij {V W} q x := by
    change (L'.piece j).val.map q.left.op
        (homSections (k.app j) _ (f.app i j hij V (homSections (u.app i) _ x))) =
      homSections (k.app j) _ (f.app i j hij W
        (homSections (u.app i) _ ((M'.piece i).val.map q.left.op x)))
    rw [homSections_naturality, f.naturality, homSections_naturality]
  map_mul i j hij p V x b := by
    change homSections (k.app (j + p)) _ (f.app (i + p) (j + p) _ V
        (homSections (u.app (i + p)) _ (M'.smul i p (Opposite.op V.left) x b))) =
      L'.smul j p (Opposite.op V.left)
        (homSections (k.app j) _ (f.app i j hij V (homSections (u.app i) _ x))) b
    rw [homSections_apply, homSections_apply (u.app (i + p)), u.map_smul, f.map_mul,
      homSections_apply, k.map_smul]
    rfl

/-- The value of `f.precompPostcomp u k` on `x` is `k (f (u x))`. -/
@[simp]
theorem GradedLocalHom.precompPostcomp_app (u : M' ⟶ M) (k : L ⟶ L') {n : ℤ} {U : C}
    (f : GradedLocalHom M L n U) (i j : ℤ) (hij : i + n = j) (V : Over U)
    (x : (M'.piece i).val.obj (Opposite.op V.left)) :
    (f.precompPostcomp u k).app i j hij V x =
      (k.app j).val.app (Opposite.op V.left)
        (f.app i j hij V ((u.app i).val.app (Opposite.op V.left) x)) := rfl

/-- Composing with morphisms of graded modules commutes with restriction. -/
theorem GradedLocalHom.precompPostcomp_restrict (u : M' ⟶ M) (k : L ⟶ L') {n : ℤ} {U U' : C}
    (q : U' ⟶ U) (f : GradedLocalHom M L n U) :
    (f.precompPostcomp u k).restrict q = (f.restrict q).precompPostcomp u k := rfl

end LocalComposition

/-! ### Morphisms of internal homs -/

section InternalHomMap

variable {M M' : GradedModule.{t, a, w} A} {L L' : GradedModule.{t, a, z} A}
  {G G' : ℤ → SheafOfModules.{g} R}

/-- The morphism `SheafHom^n(M, L) ⟶ SheafHom^n(M', L')` of sheaves of `R`-modules induced by
morphisms `u : M' ⟶ M` and `k : L ⟶ L'` of right graded modules: on sections it is
`f ↦ k ∘ f ∘ u`. -/
noncomputable def IsGradedSheafHom.map (hG : IsGradedSheafHom M L G)
    (hG' : IsGradedSheafHom M' L' G') (u : M' ⟶ M) (k : L ⟶ L') (n : ℤ) : G n ⟶ G' n where
  val :=
    { app := fun U => ModuleCat.ofHom
        { toFun := fun p => (hG'.sectionsEquiv n U.unop).symm
            ((hG.sectionsEquiv n U.unop p).precompPostcomp u k)
          map_add' := fun p q => hG'.symm_add n U.unop _ _ _ fun i j hij V x => by
            rw [GradedLocalHom.precompPostcomp_app, GradedLocalHom.precompPostcomp_app,
              GradedLocalHom.precompPostcomp_app, hG.sectionsEquiv_add]
            exact map_add _ _ _
          map_smul' := fun r p => hG'.symm_smul n U.unop r _ _ fun i j hij V x => by
            rw [GradedLocalHom.precompPostcomp_app, GradedLocalHom.precompPostcomp_app,
              hG.sectionsEquiv_smul]
            exact (k.app j).val.app _ |>.hom.map_smul _ _ }
      naturality := fun {U V} γ => ModuleCat.hom_ext (LinearMap.ext fun p => by
        have hres : hG.sectionsEquiv n V.unop ((G n).val.map γ p) =
            (hG.sectionsEquiv n U.unop p).restrict γ.unop :=
          GradedLocalHom.ext fun i j hij W x =>
            DFunLike.congr_fun (hG.sectionsEquiv_naturality n γ.unop p i j hij W) x
        change (hG'.sectionsEquiv n V.unop).symm
            ((hG.sectionsEquiv n V.unop ((G n).val.map γ p)).precompPostcomp u k) =
          (G' n).val.map γ.unop.op ((hG'.sectionsEquiv n U.unop).symm
            ((hG.sectionsEquiv n U.unop p).precompPostcomp u k))
        rw [hres, ← GradedLocalHom.precompPostcomp_restrict, hG'.symm_naturality]) }

/-- The morphism `IsGradedSheafHom.map hG hG' u k n` sends the section naming a local
homomorphism `f` to the section naming `k ∘ f ∘ u`. -/
theorem IsGradedSheafHom.sectionsEquiv_map (hG : IsGradedSheafHom M L G)
    (hG' : IsGradedSheafHom M' L' G') (u : M' ⟶ M) (k : L ⟶ L') (n : ℤ) (U : C)
    (p : (G n).val.obj (Opposite.op U)) :
    hG'.sectionsEquiv n U ((hG.map hG' u k n).val.app (Opposite.op U) p) =
      (hG.sectionsEquiv n U p).precompPostcomp u k :=
  Equiv.apply_symm_apply _ _

end InternalHomMap

section BimoduleInternalHomMap

variable {N N' : GradedBimodule.{t, a, z} A B} {L L' : GradedModule.{t, a, s} B}
  {H H' : GradedModule.{t, a, w} A}

/-- The morphism `SheafHom^gr_B(N, L) ⟶ SheafHom^gr_B(N', L')` of right graded `A`-modules
induced by a morphism `σ : N' ⟶ N` of graded `(A, B)`-bimodules and a morphism `k : L ⟶ L'` of
right graded `B`-modules: on sections it is `f ↦ k ∘ f ∘ σ`. -/
noncomputable def IsGradedInternalHom.map (hH : IsGradedInternalHom N L H)
    (hH' : IsGradedInternalHom N' L' H') (σ : N' ⟶ N) (k : L ⟶ L') : H ⟶ H' where
  app m := hH.toIsGradedSheafHom.map hH'.toIsGradedSheafHom
    (GradedBimodule.Hom.toGradedModuleHom σ) k m
  map_smul m p U q b := by
    obtain ⟨U⟩ := U
    refine hH'.sections_ext fun i j hij V y => ?_
    rw [hH'.sectionsEquiv_mul, IsGradedSheafHom.sectionsEquiv_map,
      IsGradedSheafHom.sectionsEquiv_map, hH.sectionsEquiv_mul]
    exact congrArg (fun z => (k.app j).val.app (Opposite.op V.left)
      ((hH.sectionsEquiv m U q).app (p + i) j (by omega) V z))
      (σ.map_leftMul p i (Opposite.op V.left) _ y).symm

/-- The morphism `IsGradedInternalHom.map hH hH' σ k` sends the section naming a local
homomorphism `f` to the section naming `k ∘ f ∘ σ`. -/
theorem IsGradedInternalHom.sectionsEquiv_map (hH : IsGradedInternalHom N L H)
    (hH' : IsGradedInternalHom N' L' H') (σ : N' ⟶ N) (k : L ⟶ L') (m : ℤ) (U : C)
    (q : (H.piece m).val.obj (Opposite.op U)) :
    hH'.sectionsEquiv m U (((hH.map hH' σ k).app m).val.app (Opposite.op U) q) =
      (hH.sectionsEquiv m U q).precompPostcomp (GradedBimodule.Hom.toGradedModuleHom σ) k :=
  IsGradedSheafHom.sectionsEquiv_map _ _ _ _ m U q

end BimoduleInternalHomMap

/-! ### Morphisms of tensor products -/

section TensorMap

variable {M M' : GradedModule.{t, a, w} A} {N N' : GradedBimodule.{t, a, z} A B}
  {T T' : GradedModule.{t, a, s} B}

/-- The `A`-balanced bilinear family `(x, y) ↦ u x ⊗ σ y` of degree zero out of `M` and `N` with
values in `M' ⊗_A N'`, over an object `U` of the site. -/
noncomputable def IsGradedTensorProduct.mapBalanced (hT' : IsGradedTensorProduct M' N' T')
    (u : M ⟶ M') (σ : N ⟶ N') (U : C) : GradedLocalBalanced M N T' 0 U where
  app i j k hijk V := (((hT'.tmul i j (Opposite.op V.left)).comp
    (homSections (u.app i) (Opposite.op V.left))).compl₂
      (homSections (σ.app j) (Opposite.op V.left))).compr₂
    (castHom T'.piece (by omega : i + j = k) (Opposite.op V.left))
  map_smul_left i j k hijk V r x y := by
    change castHom T'.piece _ _ (hT'.tmul i j _ (homSections (u.app i) _ (r • x))
        (homSections (σ.app j) _ y)) =
      r • castHom T'.piece _ _ (hT'.tmul i j _ (homSections (u.app i) _ x)
        (homSections (σ.app j) _ y))
    rw [homSections_smul, hT'.tmul_smul_left, castHom_smul]
  map_smul_right i j k hijk V r x y := by
    change castHom T'.piece _ _ (hT'.tmul i j _ (homSections (u.app i) _ x)
        (homSections (σ.app j) _ (r • y))) =
      r • castHom T'.piece _ _ (hT'.tmul i j _ (homSections (u.app i) _ x)
        (homSections (σ.app j) _ y))
    rw [homSections_smul, hT'.tmul_smul_right, castHom_smul]
  naturality i j k hijk {V W} q x y := by
    change (T'.piece k).val.map q.left.op (castHom T'.piece _ _
        (hT'.tmul i j _ (homSections (u.app i) _ x) (homSections (σ.app j) _ y))) =
      castHom T'.piece _ _ (hT'.tmul i j _
        (homSections (u.app i) (Opposite.op W.left) ((M.piece i).val.map q.left.op x))
        (homSections (σ.app j) (Opposite.op W.left) ((N.piece j).val.map q.left.op y)))
    rw [castHom_naturality, hT'.tmul_naturality, homSections_naturality,
      homSections_naturality]
  balanced i p j k hijk V x b y := by
    change castHom T'.piece _ _ (hT'.tmul (i + p) j _
        (homSections (u.app (i + p)) _ (M.smul i p (Opposite.op V.left) x b))
        (homSections (σ.app j) _ y)) =
      castHom T'.piece _ _ (hT'.tmul i (p + j) _ (homSections (u.app i) _ x)
        (homSections (σ.app (p + j)) _ ((N.leftMul p j).app (Opposite.op V.left) b y)))
    rw [homSections_apply (u.app (i + p)), u.map_smul, homSections_apply (σ.app (p + j)),
      σ.map_leftMul]
    exact castHom_congr_heq _ _ _ _ (hT'.tmul_balanced i p j _ _ b _)
  map_rightMul i j p k hijk V x y b := by
    obtain rfl : k = i + j := by omega
    change castHom T'.piece _ _ (hT'.tmul i (j + p) _ (homSections (u.app i) _ x)
        (homSections (σ.app (j + p)) _ ((N.rightMul j p).app (Opposite.op V.left) y b))) =
      T'.smul (i + j) p (Opposite.op V.left) (hT'.tmul i j _ (homSections (u.app i) _ x)
        (homSections (σ.app j) _ y)) b
    rw [homSections_apply (σ.app (j + p)), σ.map_rightMul]
    exact castHom_congr_heq _ _ rfl _ (hT'.tmul_rightMul i j p _ _ _ b).symm

/-- The degree-zero local homomorphism `(M ⊗_A N)|_U → (M' ⊗_A N')|_U` with `x ⊗ y ↦ u x ⊗ σ y`. -/
noncomputable def IsGradedTensorProduct.mapLocal (hT : IsGradedTensorProduct M N T)
    (hT' : IsGradedTensorProduct M' N' T') (u : M ⟶ M') (σ : N ⟶ N') (U : C) :
    GradedLocalHom T T' 0 U :=
  (hT.universal T' 0 U).symm (hT'.mapBalanced u σ U)

/-- The morphism `M ⊗_A N ⟶ M' ⊗_A N'` of right graded `B`-modules induced by a morphism
`u : M ⟶ M'` of right graded `A`-modules and a morphism `σ : N ⟶ N'` of graded
`(A, B)`-bimodules. It sends `x ⊗ y` to `u x ⊗ σ y` (`IsGradedTensorProduct.map_tmul`). -/
noncomputable def IsGradedTensorProduct.map (hT : IsGradedTensorProduct M N T)
    (hT' : IsGradedTensorProduct M' N' T') (u : M ⟶ M') (σ : N ⟶ N') : T ⟶ T' :=
  (GradedHomOfDegree.ofLocal (hT.mapLocal hT' u σ) (fun {U U'} q => by
    rw [IsGradedTensorProduct.mapLocal, IsGradedTensorProduct.mapLocal,
      hT.universal_symm_restrict]
    exact congrArg (hT.universal T' 0 U').symm
      (GradedLocalBalanced.ext fun _ _ _ _ _ _ _ => rfl))).toHom

/-- The induced morphism of tensor products sends `x ⊗ y` to `u x ⊗ σ y`. -/
theorem IsGradedTensorProduct.map_tmul (hT : IsGradedTensorProduct M N T)
    (hT' : IsGradedTensorProduct M' N' T') (u : M ⟶ M') (σ : N ⟶ N') (i j : ℤ) (U : C)
    (x : (M.piece i).val.obj (Opposite.op U)) (y : (N.piece j).val.obj (Opposite.op U)) :
    ((hT.map hT' u σ).app (i + j)).val.app (Opposite.op U) (hT.tmul i j (Opposite.op U) x y) =
      hT'.tmul i j (Opposite.op U) ((u.app i).val.app (Opposite.op U) x)
        ((σ.app j).val.app (Opposite.op U) y) := by
  have h := hT.universal_app T' 0 U (hT.mapLocal hT' u σ U) i j (i + j) (by omega)
    (Over.mk (𝟙 U)) x y
  rw [IsGradedTensorProduct.mapLocal, Equiv.apply_symm_apply] at h
  exact h.symm

end TensorMap

/-! ### Functoriality of the first identity -/

section FirstIdentity

variable {M M' H H' : GradedModule.{t, a, w} A} {N N' : GradedBimodule.{t, a, z} A B}
  {L L' T T' : GradedModule.{t, a, s} B}

/-- The first identity sends `φ : M ⊗_A N → L` to the homomorphism `x ↦ (y ↦ φ (x ⊗ y))`. -/
theorem tensorHomEquiv_sectionsEquiv_app (hT : IsGradedTensorProduct M N T)
    (hH : IsGradedInternalHom N L H) {n : ℤ} (φ : GradedHomOfDegree T L n) (i j : ℤ)
    (hij : i + n = j) (U : C) (x : (M.piece i).val.obj (Opposite.op U)) (j' k : ℤ)
    (hj'k : j' + j = k) (W : Over U) (y : (N.piece j').val.obj (Opposite.op W.left)) :
    (hH.sectionsEquiv j U
        (((tensorHomEquiv hT hH n φ).app i j hij).val.app (Opposite.op U) x)).app j' k hj'k W y =
      (φ.app (i + j') k (by omega)).val.app (Opposite.op W.left)
        (hT.tmul i j' (Opposite.op W.left) ((M.piece i).val.map W.hom.op x) y) := by
  change (hH.sectionsEquiv j U ((hH.sectionsEquiv j U).symm
    (balancedHom (hT.universal L n U (φ.toLocal U)) hij (Over.mk (𝟙 U)) x))).app j' k hj'k W y =
      _
  rw [Equiv.apply_symm_apply, balancedHom_eq]
  exact hT.universal_app L n U (φ.toLocal U) i j' k _ (Over.mk (W.hom ≫ (Over.mk (𝟙 U)).hom))
    ((M.piece i).val.map W.hom.op x) y

/-- **Tensor-hom adjunction for sheaves of graded modules**, first identity, functoriality in
`M`: for a morphism `u : M' ⟶ M` of right graded `A`-modules, precomposition with the induced
`u ⊗ 1 : M' ⊗_A N ⟶ M ⊗_A N` corresponds to precomposition with `u`. -/
@[stacks 0FR6 "first identity, natural in M"]
theorem tensorHomEquiv_naturality_left (hT : IsGradedTensorProduct M N T)
    (hT' : IsGradedTensorProduct M' N T') (hH : IsGradedInternalHom N L H) (u : M' ⟶ M) {n : ℤ}
    (φ : GradedHomOfDegree T L n) :
    tensorHomEquiv hT' hH n (GradedHomOfDegree.compLeft (hT'.map hT u (𝟙 N)) φ) =
      GradedHomOfDegree.compLeft u (tensorHomEquiv hT hH n φ) := by
  refine GradedHomOfDegree.ext_sections fun i j hij U x => ?_
  refine hH.sections_ext fun j' k hj'k W y => ?_
  refine (tensorHomEquiv_sectionsEquiv_app hT' hH _ i j hij U x j' k hj'k W y).trans ?_
  refine Eq.trans ?_ (tensorHomEquiv_sectionsEquiv_app hT hH φ i j hij U
    ((u.app i).val.app (Opposite.op U) x) j' k hj'k W y).symm
  exact congrArg ((φ.app (i + j') k (by omega)).val.app (Opposite.op W.left))
    ((hT'.map_tmul hT u (𝟙 N) i j' W.left ((M'.piece i).val.map W.hom.op x) y).trans
      (congrArg (fun z => hT.tmul i j' (Opposite.op W.left) z y)
        (homSections_naturality (u.app i) W.hom.op x).symm))

/-- **Tensor-hom adjunction for sheaves of graded modules**, first identity, functoriality in
`N`: for a morphism `σ : N ⟶ N'` of graded `(A, B)`-bimodules, precomposition with the induced
`1 ⊗ σ : M ⊗_A N ⟶ M ⊗_A N'` corresponds to postcomposition with the induced
`SheafHom^gr_B(N', L) ⟶ SheafHom^gr_B(N, L)`. -/
@[stacks 0FR6 "first identity, natural in N"]
theorem tensorHomEquiv_naturality_bimodule (hT : IsGradedTensorProduct M N T)
    (hT' : IsGradedTensorProduct M N' T') (hH : IsGradedInternalHom N L H)
    (hH' : IsGradedInternalHom N' L H') (σ : N ⟶ N') {n : ℤ} (φ : GradedHomOfDegree T' L n) :
    tensorHomEquiv hT hH n (GradedHomOfDegree.compLeft (hT.map hT' (𝟙 M) σ) φ) =
      (tensorHomEquiv hT' hH' n φ).compRight (hH'.map hH σ (𝟙 L)) := by
  refine GradedHomOfDegree.ext_sections fun i j hij U x => ?_
  refine hH.sections_ext fun j' k hj'k W y => ?_
  refine (tensorHomEquiv_sectionsEquiv_app hT hH _ i j hij U x j' k hj'k W y).trans ?_
  refine Eq.trans ?_ (congrArg
    (fun f : GradedLocalHom N.toGradedModule L j U => f.app j' k hj'k W y)
    (IsGradedInternalHom.sectionsEquiv_map hH' hH σ (𝟙 L) j U _)).symm
  refine Eq.trans ?_ (tensorHomEquiv_sectionsEquiv_app hT' hH' φ i j hij U x j' k hj'k W
    ((σ.app j').val.app (Opposite.op W.left) y)).symm
  exact congrArg ((φ.app (i + j') k (by omega)).val.app (Opposite.op W.left))
    (hT.map_tmul hT' (𝟙 M) σ i j' W.left ((M.piece i).val.map W.hom.op x) y)

/-- **Tensor-hom adjunction for sheaves of graded modules**, first identity, functoriality in
`L`: for a morphism `k : L ⟶ L'` of right graded `B`-modules, postcomposition with `k`
corresponds to postcomposition with the induced `SheafHom^gr_B(N, L) ⟶ SheafHom^gr_B(N, L')`. -/
@[stacks 0FR6 "first identity, natural in L"]
theorem tensorHomEquiv_naturality_right (hT : IsGradedTensorProduct M N T)
    (hH : IsGradedInternalHom N L H) (hH' : IsGradedInternalHom N L' H') (k : L ⟶ L') {n : ℤ}
    (φ : GradedHomOfDegree T L n) :
    tensorHomEquiv hT hH' n (φ.compRight k) =
      (tensorHomEquiv hT hH n φ).compRight (hH.map hH' (𝟙 N) k) := by
  refine GradedHomOfDegree.ext_sections fun i j hij U x => ?_
  refine hH'.sections_ext fun j' k' hj'k W y => ?_
  refine (tensorHomEquiv_sectionsEquiv_app hT hH' _ i j hij U x j' k' hj'k W y).trans ?_
  refine Eq.trans ?_ (congrArg
    (fun f : GradedLocalHom N.toGradedModule L' j U => f.app j' k' hj'k W y)
    (IsGradedInternalHom.sectionsEquiv_map hH hH' (𝟙 N) k j U _)).symm
  exact congrArg ((k.app k').val.app (Opposite.op W.left))
    (tensorHomEquiv_sectionsEquiv_app hT hH φ i j hij U x j' k' hj'k W y).symm

end FirstIdentity

/-! ### Functoriality of the second identity -/

section SecondIdentity

variable {M M' H H' : GradedModule.{t, a, w} A} {N N' : GradedBimodule.{t, a, z} A B}
  {L L' T T' : GradedModule.{t, a, s} B} {G G' : ℤ → SheafOfModules.{g} R}

/-- The second identity reads a section `p` of `SheafHom^gr_B(M ⊗_A N, L)` as the local
homomorphism `x ↦ (y ↦ p (x ⊗ y))`. -/
theorem isGradedSheafHom_tensor_sectionsEquiv_app (hT : IsGradedTensorProduct M N T)
    (hH : IsGradedInternalHom N L H) (hG : IsGradedSheafHom T L G) (n : ℤ) (U : C)
    (p : (G n).val.obj (Opposite.op U)) (i j : ℤ) (hij : i + n = j) (V : Over U)
    (x : (M.piece i).val.obj (Opposite.op V.left)) (j' k : ℤ) (hj'k : j' + j = k)
    (W : Over V.left) (y : (N.piece j').val.obj (Opposite.op W.left)) :
    (hH.sectionsEquiv j V.left
        (((isGradedSheafHom_tensor hT hH hG).sectionsEquiv n U p).app i j hij V x)).app
          j' k hj'k W y =
      (hG.sectionsEquiv n U p).app (i + j') k (by omega) (Over.mk (W.hom ≫ V.hom))
        (hT.tmul i j' (Opposite.op W.left) ((M.piece i).val.map W.hom.op x) y) := by
  change (hH.sectionsEquiv j V.left ((hH.sectionsEquiv j V.left).symm
    (balancedHom (hT.universal L n U (hG.sectionsEquiv n U p)) hij V x))).app j' k hj'k W y = _
  rw [Equiv.apply_symm_apply, balancedHom_eq]
  exact hT.universal_app L n U (hG.sectionsEquiv n U p) i j' k _ (Over.mk (W.hom ≫ V.hom))
    ((M.piece i).val.map W.hom.op x) y

/-- Two morphisms into a graded internal hom agree when the local homomorphisms named by the
images of every section agree. -/
private theorem map_ext_of_sectionsEquiv {A₁ : GradedAlgebra.{t, a} R}
    {M₁ : GradedModule.{t, a, w} A₁} {L₁ : GradedModule.{t, a, z} A₁}
    (hG' : IsGradedSheafHom M₁ L₁ G') {n : ℤ} {α β : G n ⟶ G' n}
    (h : ∀ (U : C) (p : (G n).val.obj (Opposite.op U)),
      hG'.sectionsEquiv n U (α.val.app (Opposite.op U) p) =
        hG'.sectionsEquiv n U (β.val.app (Opposite.op U) p)) : α = β :=
  SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun U => ModuleCat.hom_ext
    (LinearMap.ext fun p => (hG'.sectionsEquiv n U.unop).injective (h U.unop p)))

/-- **Tensor-hom adjunction for sheaves of graded modules**, second identity, functoriality in
`M`: for a morphism `u : M' ⟶ M` of right graded `A`-modules, the morphism
`SheafHom^gr_B(M ⊗_A N, L) ⟶ SheafHom^gr_B(M' ⊗_A N, L)` induced by `u ⊗ 1` is the morphism
`SheafHom^gr_A(M, SheafHom^gr_B(N, L)) ⟶ SheafHom^gr_A(M', SheafHom^gr_B(N, L))` induced by
`u`. -/
@[stacks 0FR6 "second identity, natural in M"]
theorem isGradedSheafHom_tensor_map_left (hT : IsGradedTensorProduct M N T)
    (hT' : IsGradedTensorProduct M' N T') (hH : IsGradedInternalHom N L H)
    (hG : IsGradedSheafHom T L G) (hG' : IsGradedSheafHom T' L G') (u : M' ⟶ M) (n : ℤ) :
    hG.map hG' (hT'.map hT u (𝟙 N)) (𝟙 L) n =
      (isGradedSheafHom_tensor hT hH hG).map (isGradedSheafHom_tensor hT' hH hG') u (𝟙 H) n := by
  refine map_ext_of_sectionsEquiv (isGradedSheafHom_tensor hT' hH hG') fun U p => ?_
  refine Eq.trans ?_ (IsGradedSheafHom.sectionsEquiv_map _ _ _ _ n U p).symm
  refine GradedLocalHom.ext fun i j hij V x => hH.sections_ext fun j' k hj'k W y => ?_
  refine (isGradedSheafHom_tensor_sectionsEquiv_app hT' hH hG' n U _ i j hij V x j' k hj'k W
    y).trans ?_
  refine (congrArg (fun f : GradedLocalHom T' L n U => f.app (i + j') k (by omega)
      (Over.mk (W.hom ≫ V.hom))
      (hT'.tmul i j' (Opposite.op W.left) ((M'.piece i).val.map W.hom.op x) y))
    (IsGradedSheafHom.sectionsEquiv_map hG hG' _ _ n U p)).trans ?_
  refine Eq.trans ?_ (isGradedSheafHom_tensor_sectionsEquiv_app hT hH hG n U p i j hij V
    ((u.app i).val.app (Opposite.op V.left) x) j' k hj'k W y).symm
  exact congrArg ((hG.sectionsEquiv n U p).app (i + j') k (by omega) (Over.mk (W.hom ≫ V.hom)))
    ((hT'.map_tmul hT u (𝟙 N) i j' W.left ((M'.piece i).val.map W.hom.op x) y).trans
      (congrArg (fun z => hT.tmul i j' (Opposite.op W.left) z y)
        (homSections_naturality (u.app i) W.hom.op x).symm))

/-- **Tensor-hom adjunction for sheaves of graded modules**, second identity, functoriality in
`N`: for a morphism `σ : N ⟶ N'` of graded `(A, B)`-bimodules, the morphism
`SheafHom^gr_B(M ⊗_A N', L) ⟶ SheafHom^gr_B(M ⊗_A N, L)` induced by `1 ⊗ σ` is the morphism
`SheafHom^gr_A(M, SheafHom^gr_B(N', L)) ⟶ SheafHom^gr_A(M, SheafHom^gr_B(N, L))` induced by the
morphism `SheafHom^gr_B(N', L) ⟶ SheafHom^gr_B(N, L)` which `σ` induces. -/
@[stacks 0FR6 "second identity, natural in N"]
theorem isGradedSheafHom_tensor_map_bimodule (hT : IsGradedTensorProduct M N T)
    (hT' : IsGradedTensorProduct M N' T') (hH : IsGradedInternalHom N L H)
    (hH' : IsGradedInternalHom N' L H') (hG : IsGradedSheafHom T L G)
    (hG' : IsGradedSheafHom T' L G') (σ : N ⟶ N') (n : ℤ) :
    hG'.map hG (hT.map hT' (𝟙 M) σ) (𝟙 L) n =
      (isGradedSheafHom_tensor hT' hH' hG').map (isGradedSheafHom_tensor hT hH hG) (𝟙 M)
        (hH'.map hH σ (𝟙 L)) n := by
  refine map_ext_of_sectionsEquiv (isGradedSheafHom_tensor hT hH hG) fun U p => ?_
  refine Eq.trans ?_ (IsGradedSheafHom.sectionsEquiv_map _ _ _ _ n U p).symm
  refine GradedLocalHom.ext fun i j hij V x => hH.sections_ext fun j' k hj'k W y => ?_
  refine (isGradedSheafHom_tensor_sectionsEquiv_app hT hH hG n U _ i j hij V x j' k hj'k W
    y).trans ?_
  refine (congrArg (fun f : GradedLocalHom T L n U => f.app (i + j') k (by omega)
      (Over.mk (W.hom ≫ V.hom))
      (hT.tmul i j' (Opposite.op W.left) ((M.piece i).val.map W.hom.op x) y))
    (IsGradedSheafHom.sectionsEquiv_map hG' hG _ _ n U p)).trans ?_
  refine Eq.trans ?_ (congrArg
    (fun f : GradedLocalHom N.toGradedModule L j V.left => f.app j' k hj'k W y)
    (IsGradedInternalHom.sectionsEquiv_map hH' hH σ (𝟙 L) j V.left _)).symm
  refine Eq.trans ?_ (isGradedSheafHom_tensor_sectionsEquiv_app hT' hH' hG' n U p i j hij V x
    j' k hj'k W ((σ.app j').val.app (Opposite.op W.left) y)).symm
  exact congrArg ((hG'.sectionsEquiv n U p).app (i + j') k (by omega) (Over.mk (W.hom ≫ V.hom)))
    (hT.map_tmul hT' (𝟙 M) σ i j' W.left ((M.piece i).val.map W.hom.op x) y)

/-- **Tensor-hom adjunction for sheaves of graded modules**, second identity, functoriality in
`L`: for a morphism `k : L ⟶ L'` of right graded `B`-modules, the morphism
`SheafHom^gr_B(M ⊗_A N, L) ⟶ SheafHom^gr_B(M ⊗_A N, L')` induced by `k` is the morphism
`SheafHom^gr_A(M, SheafHom^gr_B(N, L)) ⟶ SheafHom^gr_A(M, SheafHom^gr_B(N, L'))` induced by the
morphism `SheafHom^gr_B(N, L) ⟶ SheafHom^gr_B(N, L')` which `k` induces. -/
@[stacks 0FR6 "second identity, natural in L"]
theorem isGradedSheafHom_tensor_map_right (hT : IsGradedTensorProduct M N T)
    (hH : IsGradedInternalHom N L H) (hH' : IsGradedInternalHom N L' H')
    (hG : IsGradedSheafHom T L G) (hG' : IsGradedSheafHom T L' G') (k : L ⟶ L') (n : ℤ) :
    hG.map hG' (𝟙 T) k n =
      (isGradedSheafHom_tensor hT hH hG).map (isGradedSheafHom_tensor hT hH' hG') (𝟙 M)
        (hH.map hH' (𝟙 N) k) n := by
  refine map_ext_of_sectionsEquiv (isGradedSheafHom_tensor hT hH' hG') fun U p => ?_
  refine Eq.trans ?_ (IsGradedSheafHom.sectionsEquiv_map _ _ _ _ n U p).symm
  refine GradedLocalHom.ext fun i j hij V x => hH'.sections_ext fun j' k' hj'k W y => ?_
  refine (isGradedSheafHom_tensor_sectionsEquiv_app hT hH' hG' n U _ i j hij V x j' k' hj'k W
    y).trans ?_
  refine (congrArg (fun f : GradedLocalHom T L' n U => f.app (i + j') k' (by omega)
      (Over.mk (W.hom ≫ V.hom))
      (hT.tmul i j' (Opposite.op W.left) ((M.piece i).val.map W.hom.op x) y))
    (IsGradedSheafHom.sectionsEquiv_map hG hG' _ _ n U p)).trans ?_
  refine Eq.trans ?_ (congrArg
    (fun f : GradedLocalHom N.toGradedModule L' j V.left => f.app j' k' hj'k W y)
    (IsGradedInternalHom.sectionsEquiv_map hH hH' (𝟙 N) k j V.left _)).symm
  exact congrArg ((k.app k').val.app (Opposite.op W.left))
    (isGradedSheafHom_tensor_sectionsEquiv_app hT hH hG n U p i j hij V x j' k' hj'k W y).symm

end SecondIdentity

end SheafOfModules

end
