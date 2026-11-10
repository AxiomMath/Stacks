module

public import Mathlib.CategoryTheory.Sites.GlobalSections
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.InjectiveSheafVanishing
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.HomComplexAugmentation
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.PresheafSpectralSequence
public import StacksFrontier.CategoryTheory.Sites.Simplicial.CohomologySpectralSequenceTagTotal
public import StacksFrontier.Topology.Simplicial.Augmentation
public import StacksFrontier.Topology.Simplicial.CohomologySpectralSequence

/-!
# The convergence of the cohomology spectral sequence of a simplicial space

Let `X` be a simplicial topological space and `F` an abelian sheaf on `X_Zar`.  The spectral
sequence of `StacksFrontier/Topology/Simplicial/CohomologySpectralSequence.lean`, the second
spectral sequence of the double complex `A^{q,p} = I^q(X_p)` of the chosen injective resolution
`F → I^•`, has first page `E_1^{p,q} = H^q(X_p, F_p)`.  This file proves the remaining clause of
Stacks 09W6: it converges to `H^{p+q}(X_Zar, F)`, functorially in `F`.

The proof is the source's.  The rows `p ↦ I^q(X_p)` of the double complex are
`Mor_{PAb}(ℤ_{X_p}, I^q)`, the Hom complex out of the resolution `… → ℤ_{X_1} → ℤ_{X_0} → ℤ` of
Stacks 09W5 into an injective abelian presheaf (Stacks 03F6), so they are exact in positive degrees
and the augmentation `Γ(X_Zar, I^q) → I^q(X_0)` is a kernel of the first differential.  Stacks 0133
then identifies the cohomology of the total complex with that of `Γ(X_Zar, I^•)`, which is
`H^n(X_Zar, F)`; and the filtration of the total complex by the simplicial degree, which is the one
the spectral sequence is built from, gives the functorial filtered abutment.

## Main definitions

* `Stacks.Topology.Simplicial.globalSectionsAugmentation`: the restriction
  `Γ(X_Zar, F) → F(X_0)`, natural in the abelian sheaf `F`; global sections are Mathlib's
  `CategoryTheory.Sheaf.Γ`, which exists because limits over `X_Zar` are limits over the simplex
  category (`hasLimitsOfShape_simplicialOpen_op`).
* `Stacks.Topology.Simplicial.freeRepresentable`: the free abelian presheaf `ℤ_U` on the presheaf
  represented by a simplicial open `U`, and `wholeSpaceFreeComplex`, the complex
  `… → ℤ_{X_1} → ℤ_{X_0}` of Stacks 09W5 in the coefficient universe.
* `Stacks.Topology.Simplicial.simplicialFiltrationFunctor`: `H^n` of the total complex with its
  filtration by the simplicial degree, as a functor of the sheaf.

## Main results

* `Stacks.Topology.Simplicial.isLimitGlobalSectionsAugmentation`: `Γ(X_Zar, F)` is the kernel of
  `F(X_0) → F(X_1)`.
* `Stacks.Topology.Simplicial.sheafWholeSpaceSectionsComplexNat_exactAt_of_injective`: for an
  injective abelian sheaf `I`, the complex `I(X_0) → I(X_1) → …` is exact in positive degrees.
* `Stacks.Topology.Simplicial.cohomologyDoubleComplexHypotheses`: the hypotheses of Stacks 0133
  for the double complex.
* `Stacks.Topology.Simplicial.cohomologySpectralSequence_abutmentIso`: the cohomology of the total
  complex is `H^n(X_Zar, F)`, naturally in `F`.
* `Stacks.Topology.Simplicial.cohomologySpectralSequence_abutment`: **Stacks 09W6, the
  convergence**: the spectral sequence converges to `H^{p+q}(X_Zar, F)`, functorially in `F`.

Together with `Stacks.Topology.Simplicial.cohomologySpectralSequence` (the spectral sequence,
functorial in `F`) and `Stacks.Topology.Simplicial.cohomologySpectralSequence_pageOneIso` (its
first page), this is the whole of Stacks 09W6.

## Implementation notes

`H^n(X_Zar, F)` is the `n`-th right derived functor of `CategoryTheory.Sheaf.Γ`, the right adjoint
of the constant sheaf functor, which is the topos-theoretic global sections functor of the source.

The free abelian presheaves of Stacks 09W5 take values in abelian groups of the smallest universe,
the morphisms of `X_Zar` lying there; they are lifted to the coefficient universe, lifting being
exact, and `freeRepresentableHomIso` is the additive Yoneda lemma for the lifted presheaves.

The filtered-abutment part follows
`StacksFrontier/CategoryTheory/Sites/Hypercovering/SpectralSequence.lean` with the start page `1` in
place of `2`; `Stacks.Cohomology.Leray.FunctorialFirstQuadrantAbutsTo` is stated for any start
page.

## References

* [Stacks Project, Tag 09W6](https://stacks.math.columbia.edu/tag/09W6)
* [Stacks Project, Tag 09W5](https://stacks.math.columbia.edu/tag/09W5)
* [Stacks Project, Tag 03F6](https://stacks.math.columbia.edu/tag/03F6)
* [Stacks Project, Tag 0133](https://stacks.math.columbia.edu/tag/0133)
* [Stacks Project, Tag 012W](https://stacks.math.columbia.edu/tag/012W)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicTopology
open scoped Simplicial

universe u w

namespace Stacks.Topology.Simplicial

variable (X : SimplicialObject TopCat.{u})

/-! ### Global sections on `X_Zar` -/

/-- The simplicial degree of a simplicial open, as a functor out of the opposite of the site of a
simplicial topological space.  It is right adjoint to the whole spaces `[n] ↦ X_n`. -/
def degreeFunctor : (SimplicialOpen X)ᵒᵖ ⥤ SimplexCategory where
  obj U := U.unop.degree.unop
  map f := f.unop.base.unop
  map_id _ := rfl
  map_comp _ _ := rfl

/-- **The whole spaces are left adjoint to the degree.**  A morphism from the simplicial open
`U ⊆ X_m` to the whole space `X_n` is a simplex map `[n] → [m]` and nothing else, the inclusion
condition being automatic. -/
def wholeSpaceAdjunction : (wholeSpaceFunctor X).rightOp ⊣ degreeFunctor X :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun m U =>
        { toFun := fun f => f.unop.base.unop
          invFun := fun g => Quiver.Hom.op
            (show U.unop ⟶ (wholeSpaceFunctor X).obj (op m) from ⟨g.op, fun _ _ => trivial⟩)
          left_inv := fun _ => Quiver.Hom.unop_inj (SimplicialOpen.Hom.ext _ _ rfl)
          right_inv := fun _ => rfl }
      homEquiv_naturality_left_symm := fun _ _ =>
        Quiver.Hom.unop_inj (SimplicialOpen.Hom.ext _ _ rfl)
      homEquiv_naturality_right := fun _ _ => rfl }

/-- The functor sending `[n]` to the whole space `X_n`, viewed in the opposite of the site of
`X`, is initial. -/
instance wholeSpaceFunctor_rightOp_initial : (wholeSpaceFunctor X).rightOp.Initial :=
  Functor.initial_of_adjunction (wholeSpaceAdjunction X)

/-- **Limits over the site of a simplicial space are limits over the simplex category**, the
whole spaces being initial; in particular abelian groups have them in every universe. -/
instance hasLimitsOfShape_simplicialOpen_op (A : Type*) [Category A]
    [HasLimitsOfShape SimplexCategory A] : HasLimitsOfShape (SimplicialOpen X)ᵒᵖ A :=
  Functor.Initial.hasLimitsOfShape_of_initial (wholeSpaceFunctor X).rightOp

/-- The vertex `1` of the one-simplex is the coface `δ 0 : [0] → [1]`. -/
lemma δ_zero_eq_const : SimplexCategory.δ (0 : Fin 2) = SimplexCategory.const ⦋0⦌ ⦋1⦌ 1 := by
  ext i; fin_cases i; rfl

/-- The vertex `0` of the one-simplex is the coface `δ 1 : [0] → [1]`. -/
lemma δ_one_eq_const : SimplexCategory.δ (1 : Fin 2) = SimplexCategory.const ⦋0⦌ ⦋1⦌ 0 := by
  ext i; fin_cases i; rfl

/-- The first differential of the complex of sections over the whole spaces is the alternating
coface differential of the cosimplicial group `[n] ↦ P(X_n)`. -/
lemma wholeSpaceSectionsComplex_d_zero_one (P : (SimplicialOpen X)ᵒᵖ ⥤ Ab.{w}) :
    ((wholeSpaceSectionsComplex.{u, w} X).obj P).d 0 1 =
      AlternatingCofaceMapComplex.objD ((wholeSpaceSectionsCosimplicial X Ab.{w}).obj P) 0 :=
  CochainComplex.of_d (fun n => ((wholeSpaceSectionsCosimplicial X Ab.{w}).obj P).obj ⦋n⦌)
    (AlternatingCofaceMapComplex.objD _) 0

/-- A morphism into degree zero of a cosimplicial abelian group is killed by the first alternating
coface differential exactly when it is equalized by the two vertices of the one-simplex. -/
lemma comp_objD_zero_eq_zero_iff (D : CosimplicialObject Ab.{w}) {W : Ab.{w}}
    (k : W ⟶ D.obj ⦋0⦌) :
    k ≫ AlternatingCofaceMapComplex.objD D 0 = 0 ↔
      k ≫ D.map (SimplexCategory.const ⦋0⦌ ⦋1⦌ 0) =
        k ≫ D.map (SimplexCategory.const ⦋0⦌ ⦋1⦌ 1) := by
  have h : AlternatingCofaceMapComplex.objD D 0 = D.δ 0 - D.δ 1 := by
    simp [AlternatingCofaceMapComplex.objD, Fin.sum_univ_succ, sub_eq_add_neg]
  rw [h, CosimplicialObject.δ, CosimplicialObject.δ, δ_zero_eq_const, δ_one_eq_const,
    Preadditive.comp_sub, sub_eq_zero, eq_comm]

/-- The differentials of the complex of sections over the whole spaces are the alternating
coface differentials of the cosimplicial group `[n] ↦ P(X_n)`. -/
lemma wholeSpaceSectionsComplex_d (P : (SimplicialOpen X)ᵒᵖ ⥤ Ab.{w}) (i : ℕ) :
    ((wholeSpaceSectionsComplex.{u, w} X).obj P).d i (i + 1) =
      AlternatingCofaceMapComplex.objD ((wholeSpaceSectionsCosimplicial X Ab.{w}).obj P) i :=
  CochainComplex.of_d (fun n => ((wholeSpaceSectionsCosimplicial X Ab.{w}).obj P).obj ⦋n⦌)
    (AlternatingCofaceMapComplex.objD _) i

section GlobalSections

variable [HasSheafify (SimplicialOpen.grothendieckTopology X) Ab.{w}]

/-- Global sections on `X_Zar` are additive, being a right adjoint. -/
instance additive_sheafΓ : (Sheaf.Γ (SimplicialOpen.grothendieckTopology X) Ab.{w}).Additive :=
  haveI : PreservesLimitsOfSize.{0, 0} (Sheaf.Γ (SimplicialOpen.grothendieckTopology X) Ab.{w}) :=
    (constantSheafΓAdj (SimplicialOpen.grothendieckTopology X) Ab.{w}).rightAdjoint_preservesLimits
  haveI : HasBinaryProducts ((SimplicialOpen X)ᵒᵖ ⥤ Ab.{w}) := functorCategoryHasLimitsOfShape
  haveI : HasBinaryProducts (Sheaf (SimplicialOpen.grothendieckTopology X) Ab.{w}) :=
    hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape
      (sheafToPresheaf (SimplicialOpen.grothendieckTopology X) Ab.{w})
  haveI : (Sheaf.Γ (SimplicialOpen.grothendieckTopology X) Ab.{w}).IsRightAdjoint :=
    ⟨_, ⟨constantSheafΓAdj (SimplicialOpen.grothendieckTopology X) Ab.{w}⟩⟩
  haveI : (Sheaf.Γ (SimplicialOpen.grothendieckTopology X) Ab.{w}).PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_isRightAdjoint _
  Functor.additive_of_preserves_binary_products _

/-- The whole space `X_0` in simplicial degree zero, as an object of the opposite of the site. -/
abbrev wholeSpaceZero : (SimplicialOpen X)ᵒᵖ := op ((wholeSpaceFunctor X).obj (op ⦋0⦌))

/-- **The augmentation `Γ(X_Zar, F) → F(X_0)`**: restriction of a global section of an abelian
sheaf on `X_Zar` to the whole space in degree zero, naturally in the sheaf. -/
abbrev globalSectionsAugmentation :
    Sheaf.Γ (SimplicialOpen.grothendieckTopology X) Ab.{w} ⟶
      (sheafSections (SimplicialOpen.grothendieckTopology X) Ab.{w}).obj (wholeSpaceZero X) :=
  Sheaf.natTransΓRes _ _ _

/-- The augmentation followed by the first differential of the complex of sections over the
whole spaces is zero: a global section has the same restriction along both vertices of `X_1`. -/
lemma globalSectionsAugmentation_comp_d
    (F : Sheaf (SimplicialOpen.grothendieckTopology X) Ab.{w}) :
    (globalSectionsAugmentation.{u, w} X).app F ≫
      ((sheafWholeSpaceSectionsComplexNat.{u, w} X).obj F).d 0 1 = 0 := by
  let D := (wholeSpaceSectionsCosimplicial X Ab.{w}).obj F.obj
  have h := (comp_objD_zero_eq_zero_iff D
    (F.ΓRes (wholeSpaceZero X) : (Sheaf.Γ _ Ab.{w}).obj F ⟶ D.obj ⦋0⦌)).2
    ((F.ΓRes_map _).trans (F.ΓRes_map _).symm)
  rwa [← wholeSpaceSectionsComplex_d_zero_one] at h

/-- **The global sections on `X_Zar` are the kernel of the first differential**: the restriction
`Γ(X_Zar, F) → F(X_0)` exhibits the global sections of an abelian sheaf as the equalizer of the
two restrictions to `X_1`.  The whole spaces `[n] ↦ X_n` are initial in the opposite of the site,
so the global sections are the limit of the cosimplicial group `[n] ↦ F(X_n)`, and a limit over the
simplex category is that equalizer.  This is the degree-zero half of the assertion in the proof
of Stacks 09W6 that the rows of the double complex evaluate to `Γ(X_Zar, I^q)` in degree `0`. -/
def isLimitGlobalSectionsAugmentation
    (F : Sheaf (SimplicialOpen.grothendieckTopology X) Ab.{w}) :
    IsLimit (KernelFork.ofι _ (globalSectionsAugmentation_comp_d.{u, w} X F)) := by
  let D := (wholeSpaceSectionsCosimplicial X Ab.{w}).obj F.obj
  let c := (Sheaf.coneΓ F).whisker (wholeSpaceFunctor X).rightOp
  let hc : IsLimit c := (Functor.Initial.isLimitWhiskerEquiv _ _).symm (Sheaf.isLimitConeΓ F)
  have hw : ∀ {W : Ab.{w}} (k : W ⟶ D.obj ⦋0⦌),
      k ≫ ((sheafWholeSpaceSectionsComplexNat.{u, w} X).obj F).d 0 1 = 0 →
        k ≫ D.map (SimplexCategory.const ⦋0⦌ ⦋1⦌ 0) =
          k ≫ D.map (SimplexCategory.const ⦋0⦌ ⦋1⦌ 1) := fun k hk => by
    have hk' : k ≫ ((wholeSpaceSectionsComplex.{u, w} X).obj F.obj).d 0 1 = 0 := hk
    rw [wholeSpaceSectionsComplex_d_zero_one] at hk'
    exact (comp_objD_zero_eq_zero_iff D k).1 hk'
  have hleg : ∀ n : SimplexCategory,
      c.π.app n = c.π.app ⦋0⦌ ≫ D.map (SimplexCategory.const ⦋0⦌ n 0) := fun n =>
    (c.w (SimplexCategory.const ⦋0⦌ n 0)).symm
  let s : ∀ {W : Ab.{w}} (k : W ⟶ D.obj ⦋0⦌),
      k ≫ ((sheafWholeSpaceSectionsComplexNat.{u, w} X).obj F).d 0 1 = 0 → Cone D :=
    fun k hk => Cone.extend (Augmentation.cosimplicialEqualizerCone D)
      (equalizer.lift k (hw k hk))
  have hs : ∀ {W : Ab.{w}} (k : W ⟶ D.obj ⦋0⦌)
      (hk : k ≫ ((sheafWholeSpaceSectionsComplexNat.{u, w} X).obj F).d 0 1 = 0)
      (n : SimplexCategory), (s k hk).π.app n = k ≫ D.map (SimplexCategory.const ⦋0⦌ n 0) :=
    fun k hk n => by
      change equalizer.lift k (hw k hk) ≫ equalizer.ι _ _ ≫ _ = _
      rw [equalizer.lift_ι_assoc]
  refine KernelFork.IsLimit.ofι _ _ (fun {W} k hk => hc.lift (s k hk))
    (fun {W} k hk => ?_) (fun {W} k hk m hm => ?_)
  · exact (hc.fac (s k hk) ⦋0⦌).trans ((hs k hk ⦋0⦌).trans (by
      rw [SimplexCategory.const_eq_id, D.map_id]
      exact Category.comp_id k))
  · refine hc.hom_ext fun n => ((?_ : m ≫ c.π.app n = _).trans (hs k hk n).symm).trans
      (hc.fac (s k hk) n).symm
    rw [hleg n, ← hm]
    exact (Category.assoc _ _ _).symm

/-- The augmentation `Γ(X_Zar, F) → F(X_0)` is a monomorphism. -/
lemma mono_globalSectionsAugmentation_app
    (F : Sheaf (SimplicialOpen.grothendieckTopology X) Ab.{w}) :
    Mono ((globalSectionsAugmentation.{u, w} X).app F) :=
  Fork.IsLimit.mono (isLimitGlobalSectionsAugmentation.{u, w} X F)

/-- The sequence `0 → Γ(X_Zar, F) → F(X_0) → F(X_1)` is exact at `F(X_0)`. -/
lemma exact_globalSectionsAugmentation
    (F : Sheaf (SimplicialOpen.grothendieckTopology X) Ab.{w}) :
    (ShortComplex.mk _ _ (globalSectionsAugmentation_comp_d.{u, w} X F)).Exact :=
  ShortComplex.exact_of_f_is_kernel _ (isLimitGlobalSectionsAugmentation.{u, w} X F)

end GlobalSections

/-! ### The rows of the double complex are exact for an injective sheaf -/

section Rows

/-- `ℤ_U`: the free abelian presheaf on the presheaf represented by a simplicial open `U`, lifted
to the coefficient universe. -/
def freeRepresentable : SimplicialOpen X ⥤ ((SimplicialOpen X)ᵒᵖ ⥤ Ab.{w}) :=
  yoneda ⋙ (Functor.whiskeringRight _ _ _).obj
    (AddCommGrpCat.free.{0} ⋙ AddCommGrpCat.uliftFunctor.{w, 0})

variable {X}

/-- The generator `s` of the free abelian group on `S`, lifted to the coefficient universe. -/
abbrev uliftFreeGen {S : Type} (s : S) :
    AddCommGrpCat.uliftFunctor.{w, 0}.obj (AddCommGrpCat.free.obj S) :=
  ULift.up (FreeAbelianGroup.of s)

/-- Two morphisms out of a lifted free abelian group agree as soon as they agree on the
generators. -/
lemma uliftFree_hom_ext {S : Type} {B : Ab.{w}}
    {α β : AddCommGrpCat.uliftFunctor.{w, 0}.obj (AddCommGrpCat.free.obj S) ⟶ B}
    (h : ∀ s : S, α.hom (uliftFreeGen s) = β.hom (uliftFreeGen s)) : α = β := by
  ext ⟨a⟩
  induction a using FreeAbelianGroup.induction_on with
  | zero => exact (map_zero α.hom).trans (map_zero β.hom).symm
  | of s => exact h s
  | neg a ha =>
    exact (map_neg α.hom (uliftFreeGen a)).trans
      ((congrArg Neg.neg ha).trans (map_neg β.hom (uliftFreeGen a)).symm)
  | add a b ha hb =>
    exact (map_add α.hom (ULift.up a) (ULift.up b)).trans
      ((congrArg₂ (· + ·) ha hb).trans (map_add β.hom (ULift.up a) (ULift.up b)).symm)

/-- The generator `𝟙 U` of `ℤ_U` over `U`. -/
abbrev freeRepresentableGen (U : SimplicialOpen X) :
    ((freeRepresentable.{u, w} X).obj U).obj (op U) :=
  uliftFreeGen (S := U ⟶ U) (𝟙 U)

/-- A restriction map of `ℤ_U` sends the generator to the restricting morphism. -/
lemma freeRepresentable_map_gen {U : SimplicialOpen X} {V : (SimplicialOpen X)ᵒᵖ}
    (g : V.unop ⟶ U) :
    (((freeRepresentable.{u, w} X).obj U).map g.op).hom (freeRepresentableGen U) =
      uliftFreeGen (S := V.unop ⟶ U) g := by
  change ULift.up (FreeAbelianGroup.map ((yoneda.obj U).map g.op) (FreeAbelianGroup.of (𝟙 U))) =
    _
  rw [FreeAbelianGroup.map_of_apply]
  exact congrArg (fun h => ULift.up (FreeAbelianGroup.of h)) (Category.comp_id g)

/-- `ℤ_U` applied to a morphism `U ⟶ U'` sends the generator to that morphism. -/
lemma freeRepresentable_map_app_gen {U U' : SimplicialOpen X} (g : U ⟶ U') :
    (((freeRepresentable.{u, w} X).map g).app (op U)).hom (freeRepresentableGen U) =
      uliftFreeGen (S := U ⟶ U') g := by
  change ULift.up (FreeAbelianGroup.map (fun h => h ≫ g) (FreeAbelianGroup.of (𝟙 U))) = _
  rw [FreeAbelianGroup.map_of_apply]
  exact congrArg (fun h => ULift.up (FreeAbelianGroup.of h)) (Category.id_comp g)

/-- **The additive Yoneda lemma for `ℤ_U`**: a morphism of abelian presheaves out of `ℤ_U` is
determined by the image of the generator, which can be any section over `U`. -/
def freeRepresentableHomEquiv (U : SimplicialOpen X) (P : (SimplicialOpen X)ᵒᵖ ⥤ Ab.{w}) :
    ((freeRepresentable.{u, w} X).obj U ⟶ P) ≃+ P.obj (op U) where
  toFun φ := (φ.app (op U)).hom (freeRepresentableGen U)
  invFun x :=
    { app V := AddCommGrpCat.ofHom ((FreeAbelianGroup.lift fun g : V.unop ⟶ U =>
          (P.map g.op).hom x).comp AddEquiv.ulift.toAddMonoidHom)
      naturality V V' f := uliftFree_hom_ext fun g => by
        change FreeAbelianGroup.lift (fun g : V'.unop ⟶ U => (P.map g.op).hom x)
            (FreeAbelianGroup.map (fun h => f.unop ≫ h) (FreeAbelianGroup.of g)) =
          (P.map f).hom (FreeAbelianGroup.lift (fun g : V.unop ⟶ U => (P.map g.op).hom x)
            (FreeAbelianGroup.of g))
        rw [FreeAbelianGroup.map_of_apply, FreeAbelianGroup.lift_apply_of,
          FreeAbelianGroup.lift_apply_of, op_comp, Functor.map_comp]
        rfl }
  left_inv φ := by
    ext V : 2
    refine uliftFree_hom_ext fun g => ?_
    exact ((FreeAbelianGroup.lift_apply_of _ g).trans
      (ConcreteCategory.congr_hom (φ.naturality (Quiver.Hom.op g)) _).symm).trans
        (congrArg (φ.app V).hom (freeRepresentable_map_gen (V := V) g))
  right_inv x := by
    change FreeAbelianGroup.lift (fun g : U ⟶ U => (P.map g.op).hom x)
      (FreeAbelianGroup.of (𝟙 U)) = x
    rw [FreeAbelianGroup.lift_apply_of, op_id, P.map_id]
    rfl
  map_add' φ ψ := rfl

variable (X) in
/-- **`Hom(ℤ_U, P) = P(U)`, naturally in `U`**, as an isomorphism of functors on the opposite of
the site; the two sides live in different universes, which the lift aligns. -/
def freeRepresentableHomIso (P : (SimplicialOpen X)ᵒᵖ ⥤ Ab.{w}) :
    (freeRepresentable.{u, w} X).op ⋙ preadditiveYoneda.obj P ≅
      P ⋙ AddCommGrpCat.uliftFunctor.{u, w} :=
  NatIso.ofComponents
    (fun U => ((freeRepresentableHomEquiv U.unop P).trans AddEquiv.ulift.symm).toAddCommGrpIso)
    (fun {U U'} f => by
      ext φ
      refine ULift.ext ?_
      change (φ.app (op U'.unop)).hom
          ((((freeRepresentable.{u, w} X).map f.unop).app (op U'.unop)).hom
            (freeRepresentableGen U'.unop)) =
        (P.map f).hom ((φ.app (op U.unop)).hom (freeRepresentableGen U.unop))
      exact ((congrArg (φ.app (op U'.unop)).hom (freeRepresentable_map_app_gen f.unop)).trans
        (congrArg (φ.app (op U'.unop)).hom (freeRepresentable_map_gen (V := U') f.unop)).symm).trans
          (ConcreteCategory.congr_hom (φ.naturality f) _))

variable (X)

/-- The complex `… → ℤ_{X_2} → ℤ_{X_1} → ℤ_{X_0}` of abelian presheaves on `X_Zar`, with
boundary the alternating sum of the face maps: the resolution of Stacks 09W5, in the coefficient
universe. -/
def wholeSpaceFreeComplex : ChainComplex ((SimplicialOpen X)ᵒᵖ ⥤ Ab.{w}) ℕ :=
  AlternatingFaceMapComplex.obj (wholeSpaceFunctor X ⋙ freeRepresentable.{u, w} X)

/-- **Stacks 09W5, in the coefficient universe**: `… → ℤ_{X_1} → ℤ_{X_0}` is exact in positive
degrees.  It is the resolution of Stacks 09W5 with the free abelian groups lifted to the
coefficient universe, and lifting is exact. -/
lemma isZero_wholeSpaceFreeComplex_homology (n : ℕ) (hn : 0 < n) :
    IsZero ((wholeSpaceFreeComplex.{u, w} X).homology n) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  let U := (Functor.whiskeringRight (SimplicialOpen X)ᵒᵖ _ _).obj
    AddCommGrpCat.uliftFunctor.{w, 0}
  have h0 : (AlternatingFaceMapComplex.obj (augmentedFreeAbelianPresheaf X).left).ExactAt
      (m + 1) :=
    have := freeAbelianRepresentableComplex_quasiIso_constant X
    (quasiIsoAt_iff_exactAt' (AlternatingFaceMapComplex.ε.app (augmentedFreeAbelianPresheaf X))
      (m + 1) (ChainComplex.exactAt_succ_single_obj _ m)).1 inferInstance
  have h1 : ((U.mapHomologicalComplex _).obj
      (AlternatingFaceMapComplex.obj (augmentedFreeAbelianPresheaf X).left)).ExactAt (m + 1) :=
    h0.map U
  have e : (U.mapHomologicalComplex _).obj
      (AlternatingFaceMapComplex.obj (augmentedFreeAbelianPresheaf X).left) ≅
        wholeSpaceFreeComplex.{u, w} X :=
    (alternatingFaceMapComplexCompMapHomologicalComplexIso U).app
      (augmentedFreeAbelianPresheaf X).left
  exact ((HomologicalComplex.exactAt_iff_isZero_homology _ _).1 (h1.of_iso e))

/-- The lift of the alternating coface differential of `[n] ↦ P(X_n)`, as a sum. -/
lemma uliftFunctor_map_objD (P : (SimplicialOpen X)ᵒᵖ ⥤ Ab.{w}) (i : ℕ) :
    AddCommGrpCat.uliftFunctor.{u, w}.map
        (AlternatingCofaceMapComplex.objD ((wholeSpaceSectionsCosimplicial X Ab.{w}).obj P) i) =
      ∑ k : Fin (i + 2), (-1 : ℤ) ^ (k : ℕ) • AddCommGrpCat.uliftFunctor.{u, w}.map
        (P.map ((wholeSpaceFunctor X).map (SimplexCategory.δ k).op).op) := by
  rw [AlternatingCofaceMapComplex.objD, Functor.map_sum]
  simp only [Functor.map_zsmul]
  rfl

/-- Precomposition with the alternating sum of the face maps of `[n] ↦ ℤ_{X_n}`, as a sum. -/
lemma preadditiveYoneda_map_op_sum (P : (SimplicialOpen X)ᵒᵖ ⥤ Ab.{w}) (i : ℕ) :
    (preadditiveYoneda.obj P).map (∑ k : Fin (i + 2), (-1 : ℤ) ^ (k : ℕ) •
        SimplicialObject.δ (wholeSpaceFunctor X ⋙ freeRepresentable.{u, w} X) k).op =
      ∑ k : Fin (i + 2), (-1 : ℤ) ^ (k : ℕ) • (preadditiveYoneda.obj P).map
        ((freeRepresentable.{u, w} X).map
          ((wholeSpaceFunctor X).map (SimplexCategory.δ k).op)).op := by
  rw [op_sum, Functor.map_sum]
  simp only [op_zsmul, Functor.map_zsmul]
  rfl

/-- The differential of the lifted complex of sections over the whole spaces, as a sum. -/
lemma uliftWholeSpaceSectionsComplex_d (P : (SimplicialOpen X)ᵒᵖ ⥤ Ab.{w}) (i : ℕ) :
    ((AddCommGrpCat.uliftFunctor.{u, w}.mapHomologicalComplex _).obj
        ((wholeSpaceSectionsComplex.{u, w} X).obj P)).d i (i + 1) =
      ∑ k : Fin (i + 2), (-1 : ℤ) ^ (k : ℕ) • AddCommGrpCat.uliftFunctor.{u, w}.map
        (P.map ((wholeSpaceFunctor X).map (SimplexCategory.δ k).op).op) :=
  (congrArg AddCommGrpCat.uliftFunctor.{u, w}.map
    (wholeSpaceSectionsComplex_d.{u, w} X P i)).trans (uliftFunctor_map_objD.{u, w} X P i)

/-- The differential of the Hom complex out of `… → ℤ_{X_1} → ℤ_{X_0}`, as a sum. -/
lemma homComplex_wholeSpaceFreeComplex_d (P : (SimplicialOpen X)ᵒᵖ ⥤ Ab.{w}) (i : ℕ) :
    ((ChainComplex.homComplexFunctor (wholeSpaceFreeComplex.{u, w} X)).obj P).d i (i + 1) =
      ∑ k : Fin (i + 2), (-1 : ℤ) ^ (k : ℕ) • (preadditiveYoneda.obj P).map
        ((freeRepresentable.{u, w} X).map
          ((wholeSpaceFunctor X).map (SimplexCategory.δ k).op)).op := by
  have h := congrArg (fun t => (preadditiveYoneda.obj P).map t.op)
    (AlternatingFaceMapComplex.obj_d_eq (wholeSpaceFunctor X ⋙ freeRepresentable.{u, w} X) i)
  exact h.trans (preadditiveYoneda_map_op_sum.{u, w} X P i)

/-- The degreewise identification `Hom(ℤ_{X_n}, P) = P(X_n)` commutes with the differentials. -/
lemma freeRepresentableHomIso_comm_d (P : (SimplicialOpen X)ᵒᵖ ⥤ Ab.{w}) (i : ℕ) :
    ((freeRepresentableHomIso X P).app (op ((wholeSpaceFunctor X).obj (op ⦋i⦌)))).hom ≫
        ((AddCommGrpCat.uliftFunctor.{u, w}.mapHomologicalComplex _).obj
          ((wholeSpaceSectionsComplex.{u, w} X).obj P)).d i (i + 1) =
      ((ChainComplex.homComplexFunctor (wholeSpaceFreeComplex.{u, w} X)).obj P).d i (i + 1) ≫
        ((freeRepresentableHomIso X P).app (op ((wholeSpaceFunctor X).obj (op ⦋i + 1⦌)))).hom := by
  rw [uliftWholeSpaceSectionsComplex_d, homComplex_wholeSpaceFreeComplex_d]
  refine (Preadditive.comp_sum _ _ _).trans ((Finset.sum_congr rfl fun k _ => ?_).trans
    (Preadditive.sum_comp _ _ _).symm)
  refine (Preadditive.comp_zsmul _ _ _).trans ((congrArg _ ?_).trans
    (Preadditive.zsmul_comp _ _ _).symm)
  exact ((freeRepresentableHomIso X P).hom.naturality
    ((wholeSpaceFunctor X).map (SimplexCategory.δ k).op).op).symm

/-- **The complex of sections over the whole spaces is the Hom complex out of the resolution of
Stacks 09W5**: `Hom(ℤ_{X_n}, P) = P(X_n)` in each degree, and precomposition with the alternating
sum of the face maps is the alternating sum of the restrictions along the cofaces.  This is the
identification `A^{p,q} = Mor_{PAb}(ℤ_{X_p}, I^q)` of the proof of Stacks 09W6. -/
def homComplexWholeSpaceFreeComplexIso (P : (SimplicialOpen X)ᵒᵖ ⥤ Ab.{w}) :
    (ChainComplex.homComplexFunctor (wholeSpaceFreeComplex.{u, w} X)).obj P ≅
      (AddCommGrpCat.uliftFunctor.{u, w}.mapHomologicalComplex _).obj
        ((wholeSpaceSectionsComplex.{u, w} X).obj P) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (freeRepresentableHomIso X P).app (op ((wholeSpaceFunctor X).obj (op ⦋n⦌))))
    (fun i j hij => by
      obtain rfl : i + 1 = j := hij
      exact freeRepresentableHomIso_comm_d.{u, w} X P i)

/-- **The rows of the double complex are exact in positive degrees** (Stacks 09W6, first step of
the proof): for an abelian presheaf which is injective, the complex `P(X_0) → P(X_1) → …` is
exact in every positive degree.  It is the Hom complex out of the resolution of Stacks 09W5 into
an injective object. -/
lemma wholeSpaceSectionsComplex_exactAt_of_injective (P : (SimplicialOpen X)ᵒᵖ ⥤ Ab.{w})
    [Injective P] (n : ℕ) (hn : 0 < n) :
    ((wholeSpaceSectionsComplex.{u, w} X).obj P).ExactAt n := by
  have h := (ChainComplex.exactAt_homComplexFunctor_obj (wholeSpaceFreeComplex.{u, w} X) P n
    (isZero_wholeSpaceFreeComplex_homology.{u, w} X n hn)).of_iso
      (homComplexWholeSpaceFreeComplexIso.{u, w} X P)
  exact (ShortComplex.exact_map_iff_of_faithful _ AddCommGrpCat.uliftFunctor.{u, w}).1 h

/-- **Stacks 09W6, the rows**: for an injective abelian sheaf `I` on `X_Zar`, the complex
`I(X_0) → I(X_1) → …` of sections over the whole spaces is exact in positive degrees.  An
injective abelian sheaf is an injective abelian presheaf (Stacks 03F6). -/
lemma sheafWholeSpaceSectionsComplexNat_exactAt_of_injective
    [HasSheafify (SimplicialOpen.grothendieckTopology X) Ab.{w}]
    (I : Sheaf (SimplicialOpen.grothendieckTopology X) Ab.{w}) [Injective I] (n : ℕ)
    (hn : 0 < n) : ((sheafWholeSpaceSectionsComplexNat.{u, w} X).obj I).ExactAt n :=
  have := I.injective_obj
  wholeSpaceSectionsComplex_exactAt_of_injective.{u, w} X I.obj n hn

end Rows


/-! ### The functorial filtered abutment to the cohomology of the total complex -/

section Abutment

open CochainComplex FilteredComplexSpectralSequence Stacks.Cohomology.Leray

variable [HasSheafify (SimplicialOpen.grothendieckTopology X) Ab.{w}]
  [EnoughInjectives (Sheaf (SimplicialOpen.grothendieckTopology X) Ab.{w})]

/-- The extension by zero of a complex indexed by `ℕ` vanishes in negative degrees. -/
private lemma isZero_extend_X_of_neg {C : Type*} [Category C] [HasZeroMorphisms C]
    [HasZeroObject C] (K : CochainComplex C ℕ) {j : ℤ} (hj : j < 0) :
    IsZero ((K.extend ComplexShape.embeddingUpNat).X j) :=
  HomologicalComplex.isZero_extend_X _ ComplexShape.embeddingUpNat j
    fun k => by change ((k : ℕ) : ℤ) ≠ j; omega

/-- **The double complex of a sheaf vanishes outside the first quadrant.**  The inner index is
the simplicial degree, extended by zero from `ℕ` by `sheafWholeSpaceSectionsComplex`, and the outer
one is the degree of the chosen injective resolution, extended by zero, so each negative index
kills the term on its own. -/
lemma isZero_cohomologyDoubleComplex_X_X
    (F : Sheaf (SimplicialOpen.grothendieckTopology X) Ab.{w}) (i j : ℤ) (h : i < 0 ∨ j < 0) :
    IsZero (((cohomologyDoubleComplex.{u, w} X F).X i).X j) := by
  rcases h with hi | hj
  · exact Functor.map_isZero (HomologicalComplex.eval Ab.{w} (ComplexShape.up ℤ) j)
      ((sheafWholeSpaceSectionsComplex.{u, w} X).map_isZero
        (isZero_injectiveResolutionExtend_X.{u, w} X F i hi))
  · exact isZero_extend_X_of_neg _ hj

/-- **The total complex of the double complex, filtered by the simplicial degree.**  This is
the filtered complex whose spectral sequence is the spectral sequence of the simplicial space and
whose cohomology with its induced filtration is the abutment. -/
abbrev simplicialFiltered (F : Sheaf (SimplicialOpen.grothendieckTopology X) Ab.{w}) :
    CochainComplex.Filtered Ab.{w} :=
  (cohomologyDoubleComplex.{u, w} X F).totalFiltration₂

/-- **`htop` for the filtered complex of the simplicial space**: the zeroth step of the filtration
by the simplicial degree is the whole total complex. -/
lemma isIso_simplicialFiltered_ι_f
    (F : Sheaf (SimplicialOpen.grothendieckTopology X) Ab.{w}) (n : ℤ) :
    IsIso (((simplicialFiltered.{u, w} X F).filtration.ι.app (op (0 : ℤ))).f n) :=
  HomologicalComplex₂.isIso_totalFiltration₂_ι_f _
    (fun i j hj => isZero_cohomologyDoubleComplex_X_X.{u, w} X F i j (Or.inr hj)) n

/-- **`hbot` for the filtered complex of the simplicial space**: the `p`-th step of the filtration
by the simplicial degree vanishes in total degrees below `p`. -/
lemma isZero_simplicialFiltered_obj_X
    (F : Sheaf (SimplicialOpen.grothendieckTopology X) Ab.{w}) (p n : ℤ) (hnp : n < p) :
    IsZero (((simplicialFiltered.{u, w} X F).filtration.obj (op p)).X n) :=
  HomologicalComplex₂.isZero_totalFiltration₂_obj_X _
    (fun i j hi => isZero_cohomologyDoubleComplex_X_X.{u, w} X F i j (Or.inl hi)) p n hnp

/-- **The second spectral sequence of the double complex vanishes outside the first quadrant,
before the start-page shift.**  This unshifted form is what
`CategoryTheory.SpectralSequence.hasEdgeMonoAtFrom_of_isFirstQuadrant` and its companion need, and
it is obtained from `CochainComplex.Filtered.isFirstQuadrant_of_firstQuadrantFiltration` applied to
the `HomologicalComplex₂.stepSubobject` presentation of the filtration -- the presentation
`HomologicalComplex₂.spectralSequence₂` is built on -- so that no transport is involved. -/
lemma isFirstQuadrant_simplicialSpectralSequence₂
    (F : Sheaf (SimplicialOpen.grothendieckTopology X) Ab.{w}) :
    CategoryTheory.SpectralSequence.IsFirstQuadrant (u := fun r => ((r, 1 - r) : ℤ × ℤ))
      (HomologicalComplex₂.spectralSequence₂ (cohomologyDoubleComplex.{u, w} X F)) :=
  CochainComplex.Filtered.isFirstQuadrant_of_firstQuadrantFiltration
    (simplicialFiltered.{u, w} X F)
    ((cohomologyDoubleComplex.{u, w} X F).stepSubobject fun (_ : ℤ) j => j)
    (fun p n => HomologicalComplex₂.stepSubobject_eq _ _ (fun _ _ => le_rfl)
      (fun _ _ => by omega) p n)
    (HomologicalComplex₂.cycles₂ (cohomologyDoubleComplex.{u, w} X F)) (fun _ _ _ => rfl)
    (HomologicalComplex₂.boundaries₂ (cohomologyDoubleComplex.{u, w} X F)) (fun _ _ _ => rfl)
    _ (fun rr p q n hr hn => HomologicalComplex₂.pageIso₂ _ rr p q n hr hn)
    (isIso_simplicialFiltered_ι_f.{u, w} X F)
    (isZero_simplicialFiltered_obj_X.{u, w} X F)

open CochainComplex.Filtered in
/-- The second spectral sequence of the double complex has an infinity page at every bidegree of
`ℤ × ℤ`. -/
lemma hasPageInfinityAt_simplicialSpectralSequence₂
    (F : Sheaf (SimplicialOpen.grothendieckTopology X) Ab.{w}) (x : ℤ × ℤ) :
    (HomologicalComplex₂.spectralSequence₂
      (cohomologyDoubleComplex.{u, w} X F)).HasPageInfinityAt x :=
  CategoryTheory.SpectralSequence.hasPageInfinityAt_of_isFirstQuadrant _
    (isFirstQuadrant_simplicialSpectralSequence₂.{u, w} X F) x

open CochainComplex.Filtered CategoryTheory.SpectralSequence in
/-- **The differentials into `(p, q)` have vanished for good from `stablePage p q` on**, for the
unshifted second spectral sequence of the double complex. -/
lemma hasEdgeMonoAtFrom_simplicialSpectralSequence₂
    (F : Sheaf (SimplicialOpen.grothendieckTopology X) Ab.{w}) (p q : ℕ)
    [(HomologicalComplex₂.spectralSequence₂
      (cohomologyDoubleComplex.{u, w} X F)).HasPageInfinityAt (ComplexShape.natEmb (p, q))] :
    (HomologicalComplex₂.spectralSequence₂ (cohomologyDoubleComplex.{u, w} X F)).HasEdgeMonoAtFrom
      (ComplexShape.natEmb (p, q)) (stablePage p q) :=
  hasEdgeMonoAtFrom_of_isFirstQuadrant _
    (isFirstQuadrant_simplicialSpectralSequence₂.{u, w} X F) (ComplexShape.natEmb (p, q))
    (stablePage p q) (by have := two_le_stablePage p q; omega) (natEmb_fst_lt_stablePage p q)

open CochainComplex.Filtered CategoryTheory.SpectralSequence in
/-- **The differentials out of `(p, q)` have vanished for good from `stablePage p q` on**, for the
unshifted second spectral sequence of the double complex. -/
lemma hasEdgeEpiAtFrom_simplicialSpectralSequence₂
    (F : Sheaf (SimplicialOpen.grothendieckTopology X) Ab.{w}) (p q : ℕ)
    [(HomologicalComplex₂.spectralSequence₂
      (cohomologyDoubleComplex.{u, w} X F)).HasPageInfinityAt (ComplexShape.natEmb (p, q))] :
    (HomologicalComplex₂.spectralSequence₂ (cohomologyDoubleComplex.{u, w} X F)).HasEdgeEpiAtFrom
      (ComplexShape.natEmb (p, q)) (stablePage p q) :=
  hasEdgeEpiAtFrom_of_isFirstQuadrant _
    (isFirstQuadrant_simplicialSpectralSequence₂.{u, w} X F) (ComplexShape.natEmb (p, q))
    (stablePage p q) (by have := two_le_stablePage p q; omega)
    (natEmb_snd_add_one_lt_stablePage p q)

open CochainComplex.Filtered CategoryTheory.SpectralSequence in
/-- `hasEdgeMonoAtFrom_simplicialSpectralSequence₂` after the start-page shift. -/
lemma hasEdgeMonoAtFrom_simplicialShiftStart
    (F : Sheaf (SimplicialOpen.grothendieckTopology X) Ab.{w}) (p q : ℕ)
    [((HomologicalComplex₂.spectralSequence₂ (cohomologyDoubleComplex.{u, w} X F)).shiftStart
      (show (0 : ℤ) ≤ 1 by omega)).HasPageInfinityAt (ComplexShape.natEmb (p, q))] :
    ((HomologicalComplex₂.spectralSequence₂ (cohomologyDoubleComplex.{u, w} X F)).shiftStart
      (show (0 : ℤ) ≤ 1 by omega)).HasEdgeMonoAtFrom
        (ComplexShape.natEmb (p, q)) (stablePage p q) :=
  hasEdgeMonoAtFrom_of_isFirstQuadrant _
    (shiftStart_isFirstQuadrant _ (show (0 : ℤ) ≤ 1 by omega)
      (isFirstQuadrant_simplicialSpectralSequence₂.{u, w} X F)) (ComplexShape.natEmb (p, q))
    (stablePage p q) (one_le_stablePage p q) (natEmb_fst_lt_stablePage p q)

open CochainComplex.Filtered CategoryTheory.SpectralSequence in
/-- `hasEdgeEpiAtFrom_simplicialSpectralSequence₂` after the start-page shift. -/
lemma hasEdgeEpiAtFrom_simplicialShiftStart
    (F : Sheaf (SimplicialOpen.grothendieckTopology X) Ab.{w}) (p q : ℕ)
    [((HomologicalComplex₂.spectralSequence₂ (cohomologyDoubleComplex.{u, w} X F)).shiftStart
      (show (0 : ℤ) ≤ 1 by omega)).HasPageInfinityAt (ComplexShape.natEmb (p, q))] :
    ((HomologicalComplex₂.spectralSequence₂ (cohomologyDoubleComplex.{u, w} X F)).shiftStart
      (show (0 : ℤ) ≤ 1 by omega)).HasEdgeEpiAtFrom
        (ComplexShape.natEmb (p, q)) (stablePage p q) :=
  hasEdgeEpiAtFrom_of_isFirstQuadrant _
    (shiftStart_isFirstQuadrant _ (show (0 : ℤ) ≤ 1 by omega)
      (isFirstQuadrant_simplicialSpectralSequence₂.{u, w} X F)) (ComplexShape.natEmb (p, q))
    (stablePage p q) (one_le_stablePage p q) (natEmb_snd_add_one_lt_stablePage p q)

open CochainComplex.Filtered in
/-- `hasEdgeMonoAtFrom_simplicialShiftStart` after the first-quadrant reindexing.

Stated in the `CategoryTheory.SpectralSequence.natRestrict`-of-`shiftStart` spelling rather than as
`(cohomologySpectralSequence X).obj F`, because that is the spelling
`CategoryTheory.SpectralSequence.shiftNatRestrict_pageInfinityIsoAt` asks for: the two are equal by
definition, but instance search is keyed on the head symbol and would not look through
`simplicialSpectralSequenceFunctor`. -/
lemma hasEdgeMonoAtFrom_simplicialNatRestrict
    (F : Sheaf (SimplicialOpen.grothendieckTopology X) Ab.{w}) (p q : ℕ) :
    (((HomologicalComplex₂.spectralSequence₂ (cohomologyDoubleComplex.{u, w} X F)).shiftStart
        (show (0 : ℤ) ≤ 1 by omega)).natRestrict
      (CategoryTheory.SpectralSequence.shiftStart_isFirstQuadrant _ (show (0 : ℤ) ≤ 1 by omega)
        (isFirstQuadrant_simplicialSpectralSequence₂.{u, w} X F))).HasEdgeMonoAtFrom (p, q)
      (stablePage p q) :=
  CategoryTheory.CohomologicalSpectralSequenceNat.hasEdgeMonoAtFrom _ (p, q)
    (stablePage p q) (add_one_le_stablePage p q) (one_le_stablePage p q)

open CochainComplex.Filtered in
/-- The companion of `hasEdgeMonoAtFrom_simplicialNatRestrict`, in the same spelling and for the
same reason. -/
lemma hasEdgeEpiAtFrom_simplicialNatRestrict
    (F : Sheaf (SimplicialOpen.grothendieckTopology X) Ab.{w}) (p q : ℕ) :
    (((HomologicalComplex₂.spectralSequence₂ (cohomologyDoubleComplex.{u, w} X F)).shiftStart
        (show (0 : ℤ) ≤ 1 by omega)).natRestrict
      (CategoryTheory.SpectralSequence.shiftStart_isFirstQuadrant _ (show (0 : ℤ) ≤ 1 by omega)
        (isFirstQuadrant_simplicialSpectralSequence₂.{u, w} X F))).HasEdgeEpiAtFrom (p, q)
      (stablePage p q) :=
  CategoryTheory.CohomologicalSpectralSequenceNat.hasEdgeEpiAtFrom _ (p, q)
    (stablePage p q) (add_two_le_stablePage p q) (one_le_stablePage p q)

open CochainComplex.Filtered CategoryTheory.SpectralSequence in
/-- **The infinity page of the spectral sequence of the simplicial space at `(p, q)` is the
infinity page of the second spectral sequence of the double complex at
`ComplexShape.natEmb (p, q)`**, read at the uniform stable page
`CochainComplex.Filtered.stablePage p q`.  This is
`CategoryTheory.SpectralSequence.shiftNatRestrict_pageInfinityIsoAt`. -/
def simplicialPageInfinityIso (F : Sheaf (SimplicialOpen.grothendieckTopology X) Ab.{w}) (p q : ℕ) :
    ((cohomologySpectralSequence.{u, w} X).obj F).pageInfinity (p, q) ≅
      (HomologicalComplex₂.spectralSequence₂ (cohomologyDoubleComplex.{u, w} X F)).pageInfinity
        (ComplexShape.natEmb (p, q)) :=
  haveI := hasPageInfinityAt_simplicialSpectralSequence₂.{u, w} X F
    (ComplexShape.natEmb (p, q))
  haveI := hasEdgeMonoAtFrom_simplicialSpectralSequence₂.{u, w} X F p q
  haveI := hasEdgeEpiAtFrom_simplicialSpectralSequence₂.{u, w} X F p q
  haveI := hasEdgeMonoAtFrom_simplicialShiftStart.{u, w} X F p q
  haveI := hasEdgeEpiAtFrom_simplicialShiftStart.{u, w} X F p q
  haveI := hasEdgeMonoAtFrom_simplicialNatRestrict.{u, w} X F p q
  haveI := hasEdgeEpiAtFrom_simplicialNatRestrict.{u, w} X F p q
  shiftNatRestrict_pageInfinityIsoAt (show (0 : ℤ) ≤ 1 by omega)
    (shiftStart_isFirstQuadrant _ (by omega)
      (isFirstQuadrant_simplicialSpectralSequence₂.{u, w} X F)) (p, q) (stablePage p q)

open CochainComplex.Filtered CategoryTheory.SpectralSequence in
/-- **`simplicialPageInfinityIso` is natural in the sheaf.**  Both transports -- the start-page
shift and the first-quadrant reindexing -- are read at the page
`CochainComplex.Filtered.stablePage p q`, which is admissible for every sheaf at once, and there
the two induced maps on the infinity pages are the *same* morphism of pages. -/
theorem simplicialPageInfinityIso_naturality
    {F G : Sheaf (SimplicialOpen.grothendieckTopology X) Ab.{w}} (f : F ⟶ G) (p q : ℕ) :
    Hom.mapPageInfinity ((cohomologySpectralSequence.{u, w} X).map f) (p, q) ≫
        (simplicialPageInfinityIso.{u, w} X G p q).hom =
      (simplicialPageInfinityIso.{u, w} X F p q).hom ≫
        Hom.mapPageInfinity
          (HomologicalComplex₂.spectralSequenceMap₂ (cohomologyDoubleComplexMap.{u, w} X f))
          (ComplexShape.natEmb (p, q)) := by
  have := hasPageInfinityAt_simplicialSpectralSequence₂.{u, w} X F
    (ComplexShape.natEmb (p, q))
  have := hasPageInfinityAt_simplicialSpectralSequence₂.{u, w} X G
    (ComplexShape.natEmb (p, q))
  have := hasEdgeMonoAtFrom_simplicialSpectralSequence₂.{u, w} X F p q
  have := hasEdgeEpiAtFrom_simplicialSpectralSequence₂.{u, w} X F p q
  have := hasEdgeMonoAtFrom_simplicialSpectralSequence₂.{u, w} X G p q
  have := hasEdgeEpiAtFrom_simplicialSpectralSequence₂.{u, w} X G p q
  have := hasEdgeMonoAtFrom_simplicialShiftStart.{u, w} X F p q
  have := hasEdgeEpiAtFrom_simplicialShiftStart.{u, w} X F p q
  have := hasEdgeMonoAtFrom_simplicialShiftStart.{u, w} X G p q
  have := hasEdgeEpiAtFrom_simplicialShiftStart.{u, w} X G p q
  have := hasEdgeMonoAtFrom_simplicialNatRestrict.{u, w} X F p q
  have := hasEdgeEpiAtFrom_simplicialNatRestrict.{u, w} X F p q
  have := hasEdgeMonoAtFrom_simplicialNatRestrict.{u, w} X G p q
  have := hasEdgeEpiAtFrom_simplicialNatRestrict.{u, w} X G p q
  exact shiftNatRestrict_pageInfinityIsoAt_naturality (show (0 : ℤ) ≤ 1 by omega)
    (shiftStart_isFirstQuadrant _ (by omega)
      (isFirstQuadrant_simplicialSpectralSequence₂.{u, w} X F))
    (shiftStart_isFirstQuadrant _ (by omega)
      (isFirstQuadrant_simplicialSpectralSequence₂.{u, w} X G))
    (HomologicalComplex₂.spectralSequenceMap₂ (cohomologyDoubleComplexMap.{u, w} X f)) (p, q)
    (stablePage p q) (one_le_stablePage p q)

open CochainComplex.Filtered CategoryTheory.SpectralSequence in
/-- **The canonical spectral sequence of the filtered complex of the simplicial space vanishes
outside the first quadrant.**  The same statement as
`isFirstQuadrant_simplicialSpectralSequence₂` for the other presentation of the same filtration,
the one `CochainComplex.filteredSpectralSequence` is built on. -/
lemma isFirstQuadrant_simplicialFilteredSpectralSequence
    (F : Sheaf (SimplicialOpen.grothendieckTopology X) Ab.{w}) :
    IsFirstQuadrant (u := fun r => ((r, 1 - r) : ℤ × ℤ))
      (CochainComplex.filteredSpectralSequence (simplicialFiltered.{u, w} X F)) :=
  isFirstQuadrant_of_firstQuadrantFiltration (simplicialFiltered.{u, w} X F)
    (filtrationSubobject (simplicialFiltered.{u, w} X F)) (fun _ _ => rfl)
    (cycles (simplicialFiltered.{u, w} X F).X
      (filtrationSubobject (simplicialFiltered.{u, w} X F))) (fun _ _ _ => rfl)
    (boundaries (simplicialFiltered.{u, w} X F).X
      (filtrationSubobject (simplicialFiltered.{u, w} X F))) (fun _ _ _ => rfl)
    _ (fun rr p' q' n' hr hn' => by
        subst hn'; exact pageIso (simplicialFiltered.{u, w} X F) rr p' q' hr)
    (isIso_simplicialFiltered_ι_f.{u, w} X F)
    (isZero_simplicialFiltered_obj_X.{u, w} X F)

open CochainComplex.Filtered CategoryTheory.SpectralSequence in
/-- The canonical spectral sequence of the filtered complex of the simplicial space has an infinity
page at every bidegree of `ℤ × ℤ`. -/
lemma hasPageInfinityAt_simplicialFiltered
    (F : Sheaf (SimplicialOpen.grothendieckTopology X) Ab.{w}) (x : ℤ × ℤ) :
    (CochainComplex.filteredSpectralSequence
      (simplicialFiltered.{u, w} X F)).HasPageInfinityAt x :=
  hasPageInfinityAt_of_isFirstQuadrant _
    (isFirstQuadrant_simplicialFilteredSpectralSequence.{u, w} X F) x

open CochainComplex.Filtered CategoryTheory.SpectralSequence in
/-- **The differentials into `(p, q)` have vanished for good from `stablePage p q` on**, for the
canonical spectral sequence of the filtered complex of the simplicial space. -/
lemma hasEdgeMonoAtFrom_simplicialFiltered
    (F : Sheaf (SimplicialOpen.grothendieckTopology X) Ab.{w}) (p q : ℕ)
    [(CochainComplex.filteredSpectralSequence
      (simplicialFiltered.{u, w} X F)).HasPageInfinityAt ((p : ℤ), (q : ℤ))] :
    (CochainComplex.filteredSpectralSequence
      (simplicialFiltered.{u, w} X F)).HasEdgeMonoAtFrom ((p : ℤ), (q : ℤ))
        (stablePage p q) :=
  hasEdgeMonoAtFrom_of_isFirstQuadrant _
    (isFirstQuadrant_simplicialFilteredSpectralSequence.{u, w} X F) ((p : ℤ), (q : ℤ))
    (stablePage p q) (by have := two_le_stablePage p q; omega) (add_one_le_stablePage p q)

open CochainComplex.Filtered CategoryTheory.SpectralSequence in
/-- **The differentials out of `(p, q)` have vanished for good from `stablePage p q` on**, for the
canonical spectral sequence of the filtered complex of the simplicial space. -/
lemma hasEdgeEpiAtFrom_simplicialFiltered
    (F : Sheaf (SimplicialOpen.grothendieckTopology X) Ab.{w}) (p q : ℕ)
    [(CochainComplex.filteredSpectralSequence
      (simplicialFiltered.{u, w} X F)).HasPageInfinityAt ((p : ℤ), (q : ℤ))] :
    (CochainComplex.filteredSpectralSequence
      (simplicialFiltered.{u, w} X F)).HasEdgeEpiAtFrom ((p : ℤ), (q : ℤ))
        (stablePage p q) :=
  hasEdgeEpiAtFrom_of_isFirstQuadrant _
    (isFirstQuadrant_simplicialFilteredSpectralSequence.{u, w} X F) ((p : ℤ), (q : ℤ))
    (stablePage p q) (by have := two_le_stablePage p q; omega)
    (by have := add_two_le_stablePage p q; omega)

open CochainComplex.Filtered in
/-- The filtration of the total complex by the simplicial degree is degreewise finite, so the
convergence identification of [Stacks, Tag 012W] applies to it. -/
lemma isDegreewiseFinite_simplicialFiltered
    (F : Sheaf (SimplicialOpen.grothendieckTopology X) Ab.{w}) :
    (simplicialFiltered.{u, w} X F).filtration.IsDegreewiseFinite :=
  isDegreewiseFinite_of_firstQuadrant (simplicialFiltered.{u, w} X F)
    (isIso_simplicialFiltered_ι_f.{u, w} X F)
    (isZero_simplicialFiltered_obj_X.{u, w} X F)

open CochainComplex.Filtered in
/-- **`CochainComplex.Filtered.stablePage p q` is a stable page at `(p, q)` for the filtered
complex of every sheaf simultaneously**, which is what the naturality of the convergence
identification needs. -/
lemma isStableFrom_simplicialFiltered
    (F : Sheaf (SimplicialOpen.grothendieckTopology X) Ab.{w}) (p q : ℕ) :
    IsStableFrom (simplicialFiltered.{u, w} X F)
      (filtrationSubobject (simplicialFiltered.{u, w} X F)) (p : ℤ) (q : ℤ)
      (stablePage p q) :=
  isStableFrom_of_firstQuadrant (simplicialFiltered.{u, w} X F)
    (isIso_simplicialFiltered_ι_f.{u, w} X F)
    (isZero_simplicialFiltered_obj_X.{u, w} X F)
    (p : ℤ) (q : ℤ) (stablePage p q) (one_le_stablePage p q) (add_two_le_stablePage p q)
    (add_one_le_stablePage p q)

/-- **The morphism of filtered complexes attached to a morphism of sheaves**: the total complex of
`simplicialDoubleMap` with its filtration by the simplicial degree.  Like
`simplicialDoubleMap` it is functorial only up to homotopy; what *is* functorial is the cohomology
it induces, which is `simplicialFiltrationFunctor`. -/
def simplicialFilteredMap {F G : Sheaf (SimplicialOpen.grothendieckTopology X) Ab.{w}} (f : F ⟶ G) :
    simplicialFiltered.{u, w} X F ⟶ simplicialFiltered.{u, w} X G :=
  Stacks.Cohomology.CechSpectral.totalFiltrationMap (fun (_ : ℤ) j => j) (fun _ _ => le_rfl)
    (fun _ _ => by omega) (cohomologyDoubleComplexMap.{u, w} X f)

/-- The underlying morphism of complexes of `simplicialFilteredMap f` is `Tot(A^{•,•}(f))`. -/
@[simp]
lemma simplicialFilteredMap_hom
    {F G : Sheaf (SimplicialOpen.grothendieckTopology X) Ab.{w}} (f : F ⟶ G) :
    (simplicialFilteredMap.{u, w} X f).hom =
      HomologicalComplex₂.total.map (cohomologyDoubleComplexMap.{u, w} X f) (ComplexShape.up ℤ) :=
  rfl

/-- **`H^n` of the total complex sends an identity to an identity.**
`simplicialDoubleMap (𝟙 F)` is only filtered homotopic to the identity, but the homotopy carried
inside `HomologicalComplex₂.FilteredHomotopy₂` is a homotopy of the *total* complexes, and
homology is homotopy invariant. -/
lemma homologyMap_simplicialFilteredMap_id
    (F : Sheaf (SimplicialOpen.grothendieckTopology X) Ab.{w}) (n : ℤ) :
    HomologicalComplex.homologyMap (simplicialFilteredMap.{u, w} X (𝟙 F)).hom n = 𝟙 _ := by
  rw [simplicialFilteredMap_hom,
    Exists.choose (filteredHomotopy₂_cohomologyDoubleComplexMap_id.{u, w} X F) |>.homologyMap_eq n,
    HomologicalComplex₂.total.map_id, HomologicalComplex.homologyMap_id]

/-- **`H^n` of the total complex is multiplicative.**  As with
`homologyMap_simplicialFilteredMap_id`, from the homotopy carried inside
`HomologicalComplex₂.FilteredHomotopy₂`. -/
lemma homologyMap_simplicialFilteredMap_comp
    {F G H : Sheaf (SimplicialOpen.grothendieckTopology X) Ab.{w}} (f : F ⟶ G) (g : G ⟶ H) (n : ℤ) :
    HomologicalComplex.homologyMap (simplicialFilteredMap.{u, w} X (f ≫ g)).hom n =
      HomologicalComplex.homologyMap (simplicialFilteredMap.{u, w} X f).hom n ≫
        HomologicalComplex.homologyMap (simplicialFilteredMap.{u, w} X g).hom n := by
  rw [simplicialFilteredMap_hom, simplicialFilteredMap_hom, simplicialFilteredMap_hom,
    Exists.choose (filteredHomotopy₂_cohomologyDoubleComplexMap_comp.{u, w} X f g)
      |>.homologyMap_eq n,
    HomologicalComplex₂.total.map_comp, HomologicalComplex.homologyMap_comp]

open CochainComplex.Filtered in
/-- **The `filtration` field**: `H^n(Tot(A^{•,•}))` with its induced filtration, as a
functor. -/
def simplicialFiltrationFunctor (n : ℤ) :
    Sheaf (SimplicialOpen.grothendieckTopology X) Ab.{w} ⥤
      FilteredObject Ab.{w} ℤᵒᵖ where
  obj F := (simplicialFiltered.{u, w} X F).inducedFilteredObject n
  map f := inducedFilteredObjectMap (simplicialFilteredMap.{u, w} X f) n
  map_id F := FilteredObject.hom_ext (homologyMap_simplicialFilteredMap_id.{u, w} X F n)
  map_comp f g :=
    FilteredObject.hom_ext (homologyMap_simplicialFilteredMap_comp.{u, w} X f g n)

open CochainComplex.Filtered CategoryTheory.SpectralSequence in
/-- **The transport of the infinity page across the two presentations of the filtration of the
total complex by the simplicial degree**: `HomologicalComplex₂.stepSubobject`, which
`HomologicalComplex₂.spectralSequence₂` uses, and `CochainComplex.filtrationSubobject` of
`HomologicalComplex₂.totalFiltration₂`, which `CochainComplex.filteredSpectralSequence` uses. -/
def simplicialPageInfinityTransportIso
    (F : Sheaf (SimplicialOpen.grothendieckTopology X) Ab.{w}) (p q : ℕ) :
    (HomologicalComplex₂.spectralSequence₂ (cohomologyDoubleComplex.{u, w} X F)).pageInfinity
        (ComplexShape.natEmb (p, q)) ≅
      (CochainComplex.filteredSpectralSequence
        (simplicialFiltered.{u, w} X F)).pageInfinity (ComplexShape.natEmb (p, q)) :=
  haveI := hasPageInfinityAt_simplicialSpectralSequence₂.{u, w} X F
    (ComplexShape.natEmb (p, q))
  haveI := hasPageInfinityAt_simplicialFiltered.{u, w} X F (ComplexShape.natEmb (p, q))
  pageInfinityEqToIso
    (HomologicalComplex₂.spectralSequence₂_eq_filteredSpectralSequence
      (cohomologyDoubleComplex.{u, w} X F)) (ComplexShape.natEmb (p, q))

open CochainComplex.Filtered CategoryTheory.SpectralSequence in
/-- **The transport is natural in the sheaf.**  This is
`CategoryTheory.SpectralSequence.mapPageInfinity_pageInfinityEqToIso` at the conjugation square
`HomologicalComplex₂.spectralSequenceMap₂_eqToHom`. -/
theorem simplicialPageInfinityTransportIso_naturality
    {F G : Sheaf (SimplicialOpen.grothendieckTopology X) Ab.{w}} (f : F ⟶ G) (p q : ℕ) :
    Hom.mapPageInfinity
          (HomologicalComplex₂.spectralSequenceMap₂ (cohomologyDoubleComplexMap.{u, w} X f))
          (ComplexShape.natEmb (p, q)) ≫
        (simplicialPageInfinityTransportIso.{u, w} X G p q).hom =
      (simplicialPageInfinityTransportIso.{u, w} X F p q).hom ≫
        Hom.mapPageInfinity (CochainComplex.filteredSpectralSequenceMap
          (simplicialFilteredMap.{u, w} X f)) (ComplexShape.natEmb (p, q)) := by
  have := hasPageInfinityAt_simplicialSpectralSequence₂.{u, w} X F
    (ComplexShape.natEmb (p, q))
  have := hasPageInfinityAt_simplicialSpectralSequence₂.{u, w} X G
    (ComplexShape.natEmb (p, q))
  have := hasPageInfinityAt_simplicialFiltered.{u, w} X F (ComplexShape.natEmb (p, q))
  have := hasPageInfinityAt_simplicialFiltered.{u, w} X G (ComplexShape.natEmb (p, q))
  exact mapPageInfinity_pageInfinityEqToIso _ _ _ _
    (HomologicalComplex₂.spectralSequenceMap₂_eqToHom (cohomologyDoubleComplexMap.{u, w} X f))
    (ComplexShape.natEmb (p, q))

open CochainComplex.Filtered CategoryTheory.SpectralSequence in
/-- **`E_∞^{p,q} ≅ gr^pH^{p+q}(Tot(A^{•,•}(F)))` for the canonical spectral sequence of the
filtered complex of the simplicial space**, with the stable page supplied uniformly by
`CochainComplex.Filtered.stablePage`.  This is
`CochainComplex.Filtered.canonicalPageInfinityIsoGr`. -/
def simplicialCanonicalGradedIso
    (F : Sheaf (SimplicialOpen.grothendieckTopology X) Ab.{w}) (p q : ℕ) :
    (CochainComplex.filteredSpectralSequence
        (simplicialFiltered.{u, w} X F)).pageInfinity (ComplexShape.natEmb (p, q)) ≅
      (FilteredObject.gr (p : ℤ)).obj
        ((simplicialFiltrationFunctor.{u, w} X ((p + q : ℕ) : ℤ)).obj F) :=
  haveI := hasPageInfinityAt_simplicialFiltered.{u, w} X F ((p : ℤ), (q : ℤ))
  haveI := hasEdgeMonoAtFrom_simplicialFiltered.{u, w} X F p q
  haveI := hasEdgeEpiAtFrom_simplicialFiltered.{u, w} X F p q
  canonicalPageInfinityIsoGr (simplicialFiltered.{u, w} X F)
    (isDegreewiseFinite_simplicialFiltered.{u, w} X F) (p : ℤ) (q : ℤ) (stablePage p q)
    (isStableFrom_simplicialFiltered.{u, w} X F p q)

open CochainComplex.Filtered CategoryTheory.SpectralSequence in
/-- **`simplicialCanonicalGradedIso` is natural in the sheaf.**  This is
`CochainComplex.Filtered.canonicalPageInfinityIsoGr_naturality` at the page
`CochainComplex.Filtered.stablePage p q`, which `isStableFrom_simplicialFiltered` makes stable for
every sheaf at once. -/
theorem simplicialCanonicalGradedIso_naturality
    {F G : Sheaf (SimplicialOpen.grothendieckTopology X) Ab.{w}} (f : F ⟶ G) (p q : ℕ) :
    Hom.mapPageInfinity (CochainComplex.filteredSpectralSequenceMap
          (simplicialFilteredMap.{u, w} X f)) (ComplexShape.natEmb (p, q)) ≫
        (simplicialCanonicalGradedIso.{u, w} X G p q).hom =
      (simplicialCanonicalGradedIso.{u, w} X F p q).hom ≫
        (FilteredObject.gr (p : ℤ)).map
          ((simplicialFiltrationFunctor.{u, w} X ((p + q : ℕ) : ℤ)).map f) := by
  have := hasPageInfinityAt_simplicialFiltered.{u, w} X F ((p : ℤ), (q : ℤ))
  have := hasPageInfinityAt_simplicialFiltered.{u, w} X G ((p : ℤ), (q : ℤ))
  have := hasEdgeMonoAtFrom_simplicialFiltered.{u, w} X F p q
  have := hasEdgeEpiAtFrom_simplicialFiltered.{u, w} X F p q
  have := hasEdgeMonoAtFrom_simplicialFiltered.{u, w} X G p q
  have := hasEdgeEpiAtFrom_simplicialFiltered.{u, w} X G p q
  exact canonicalPageInfinityIsoGr_naturality (simplicialFilteredMap.{u, w} X f)
    (isDegreewiseFinite_simplicialFiltered.{u, w} X F)
    (isDegreewiseFinite_simplicialFiltered.{u, w} X G) (p : ℤ) (q : ℤ) (stablePage p q)
    (isStableFrom_simplicialFiltered.{u, w} X F p q)
    (isStableFrom_simplicialFiltered.{u, w} X G p q)
    (inducedFilteredObjectMap (simplicialFilteredMap.{u, w} X f) ((p + q : ℕ) : ℤ)) rfl

open CochainComplex.Filtered CategoryTheory.SpectralSequence in
/-- **The `gradedIso` field**: `E_∞^{p,q} ≅ gr^pH^{p+q}`. -/
def simplicialGradedIso (F : Sheaf (SimplicialOpen.grothendieckTopology X) Ab.{w}) (p q : ℕ) :
    ((cohomologySpectralSequence.{u, w} X).obj F).pageInfinity (p, q) ≅
      (FilteredObject.gr (p : ℤ)).obj
        ((simplicialFiltrationFunctor.{u, w} X ((p + q : ℕ) : ℤ)).obj F) :=
  simplicialPageInfinityIso.{u, w} X F p q ≪≫
    simplicialPageInfinityTransportIso.{u, w} X F p q ≪≫
      simplicialCanonicalGradedIso.{u, w} X F p q

open CochainComplex.Filtered CategoryTheory.SpectralSequence in
/-- **The `gradedIso_naturality` field**: the three squares, pasted. -/
theorem simplicialGradedIso_naturality
    {F G : Sheaf (SimplicialOpen.grothendieckTopology X) Ab.{w}} (f : F ⟶ G) (p q : ℕ) :
    Hom.mapPageInfinity ((cohomologySpectralSequence.{u, w} X).map f) (p, q) ≫
        (simplicialGradedIso.{u, w} X G p q).hom =
      (simplicialGradedIso.{u, w} X F p q).hom ≫
        (FilteredObject.gr (p : ℤ)).map
          ((simplicialFiltrationFunctor.{u, w} X ((p + q : ℕ) : ℤ)).map f) := by
  rw [simplicialGradedIso, simplicialGradedIso]
  simp only [Iso.trans_hom, Category.assoc]
  rw [reassoc_of% simplicialPageInfinityIso_naturality.{u, w} X f p q,
    reassoc_of% simplicialPageInfinityTransportIso_naturality.{u, w} X f p q,
    simplicialCanonicalGradedIso_naturality.{u, w} X f p q]

open CochainComplex.Filtered CategoryTheory.SpectralSequence in
/-- **The functorial filtered abutment of the spectral sequence of the simplicial space, abutting
to the cohomology of the total complex.** -/
def simplicialFunctorialAbutment :
    FunctorialFirstQuadrantAbutsTo (cohomologySpectralSequence.{u, w} X)
      (fun n => simplicialFiltrationFunctor.{u, w} X (n : ℤ) ⋙ FilteredObject.forget) where
  filtration n := simplicialFiltrationFunctor.{u, w} X (n : ℤ)
  abutmentIso _ := Iso.refl _
  isFinite F n := (Filtration.isFinite_iff_subobject _).2
    ⟨⟨op (0 : ℤ), inducedFilteredObject_subobject_zero (simplicialFiltered.{u, w} X F)
        (isIso_simplicialFiltered_ι_f.{u, w} X F) (n : ℤ)⟩,
      ⟨op ((n : ℤ) + 1), inducedFilteredObject_subobject_succ
        (simplicialFiltered.{u, w} X F)
        (isZero_simplicialFiltered_obj_X.{u, w} X F) (n : ℤ)⟩⟩
  isTop F n := inducedFilteredObject_subobject_zero (simplicialFiltered.{u, w} X F)
    (isIso_simplicialFiltered_ι_f.{u, w} X F) (n : ℤ)
  isBot F n := inducedFilteredObject_subobject_succ (simplicialFiltered.{u, w} X F)
    (isZero_simplicialFiltered_obj_X.{u, w} X F) (n : ℤ)
  gradedIso F p q := simplicialGradedIso.{u, w} X F p q
  gradedIso_naturality f p q := simplicialGradedIso_naturality.{u, w} X f p q

end Abutment

/-! ### The abutment is the cohomology of `X_Zar` -/

section AbutmentIsCohomology

open CochainComplex Stacks.Cohomology.Leray

variable [HasSheafify (SimplicialOpen.grothendieckTopology X) Ab.{w}]

/-- Evaluating the complex of sections over the whole spaces, extended by zero, in degree `0`
gives the sections over `X_0`. -/
def sheafWholeSpaceSectionsComplexCompEvalZero :
    sheafWholeSpaceSectionsComplex.{u, w} X ⋙
        HomologicalComplex.eval Ab.{w} (ComplexShape.up ℤ) (0 : ℤ) ≅
      (sheafSections (SimplicialOpen.grothendieckTopology X) Ab.{w}).obj (wholeSpaceZero X) :=
  Functor.isoWhiskerLeft (sheafWholeSpaceSectionsComplexNat.{u, w} X)
    (ComplexShape.embeddingUpNat.extendFunctorCompEvalIso Ab.{w} (i := 0) (i' := (0 : ℤ)) rfl)

/-- **The augmentation `Γ(X_Zar, Z^•) ⟶ A^{•,0}` into the zeroth row of the double complex**, as
a natural transformation in the complex of abelian sheaves `Z^•`: in degree `q` it is the
restriction `Γ(X_Zar, Z^q) → Z^q(X_0)`. -/
def globalSectionsAlphaNat :
    (Sheaf.Γ (SimplicialOpen.grothendieckTopology X) Ab.{w}).mapHomologicalComplex
        (ComplexShape.up ℤ) ⟶
      cohomologyDoubleComplexFunctor.{u, w} X ⋙ rowZeroFunctor Ab.{w} :=
  NatTrans.mapHomologicalComplex (globalSectionsAugmentation.{u, w} X) (ComplexShape.up ℤ) ≫
    (NatIso.mapHomologicalComplex (sheafWholeSpaceSectionsComplexCompEvalZero.{u, w} X)
      (ComplexShape.up ℤ)).inv

/-- The augmentation into the zeroth row, at a complex of abelian sheaves. -/
abbrev globalSectionsAlpha
    (Z : CochainComplex (Sheaf (SimplicialOpen.grothendieckTopology X) Ab.{w}) ℤ) :
    ((Sheaf.Γ (SimplicialOpen.grothendieckTopology X) Ab.{w}).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj Z ⟶ rowZero ((cohomologyDoubleComplexFunctor.{u, w} X).obj Z) :=
  (globalSectionsAlphaNat.{u, w} X).app Z

/-- **The augmentation is natural in the complex of abelian sheaves.** -/
theorem globalSectionsAlpha_naturality
    {Z W : CochainComplex (Sheaf (SimplicialOpen.grothendieckTopology X) Ab.{w}) ℤ}
    (φ : Z ⟶ W) :
    globalSectionsAlpha.{u, w} X Z ≫ rowZeroMap ((cohomologyDoubleComplexFunctor.{u, w} X).map φ) =
      ((Sheaf.Γ (SimplicialOpen.grothendieckTopology X) Ab.{w}).mapHomologicalComplex
          (ComplexShape.up ℤ)).map φ ≫ globalSectionsAlpha.{u, w} X W :=
  ((globalSectionsAlphaNat.{u, w} X).naturality φ).symm

/-- **The hypotheses of Stacks 0133 for the double complex `A^{q,p} = Z^q(X_p)`** of a complex
`Z^•` of injective abelian sheaves on `X_Zar` vanishing in negative degrees.  The rows are exact
away from simplicial degree `0`, by Stacks 09W5 and Stacks 03F6
(`sheafWholeSpaceSectionsComplexNat_exactAt_of_injective`), and in simplicial degree `0` the
augmentation `Γ(X_Zar, Z^q) → Z^q(X_0)` is a kernel of the first differential
(`isLimitGlobalSectionsAugmentation`). -/
theorem cohomologyDoubleComplexHypotheses
    (Z : CochainComplex (Sheaf (SimplicialOpen.grothendieckTopology X) Ab.{w}) ℤ)
    (hZ : ∀ q : ℤ, q < 0 → IsZero (Z.X q)) (hinj : ∀ q : ℤ, Injective (Z.X q)) :
    Hypotheses (((Sheaf.Γ (SimplicialOpen.grothendieckTopology X) Ab.{w}).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj Z) ((cohomologyDoubleComplexFunctor.{u, w} X).obj Z)
      (globalSectionsAlpha.{u, w} X Z) where
  diagonalFinite n := by
    refine Set.Finite.subset (Set.finite_Icc (0 : ℤ) n) fun q hq => ?_
    simp only [Set.mem_ofPred_eq] at hq
    refine Set.mem_Icc.2 ⟨?_, ?_⟩
    · by_contra h
      exact hq ((HomologicalComplex.eval Ab.{w} (ComplexShape.up ℤ) (n - q)).map_isZero
        ((sheafWholeSpaceSectionsComplex.{u, w} X).map_isZero (hZ q (by omega))))
    · by_contra h
      exact hq (isZero_extend_X_of_neg _ (by omega))
  zero_of_neg q p hp := isZero_extend_X_of_neg _ hp
  exactAt_of_ne_zero q p hp := by
    rcases lt_trichotomy p 0 with h | h | h
    · exact HomologicalComplex.extend_exactAt _ ComplexShape.embeddingUpNat p
        fun j => by change ((j : ℕ) : ℤ) ≠ p; omega
    · exact absurd h hp
    · have hk : ComplexShape.embeddingUpNat.f p.toNat = p := by
        change ((p.toNat : ℕ) : ℤ) = p; omega
      refine (HomologicalComplex.extend_exactAt_iff _ ComplexShape.embeddingUpNat hk).2 ?_
      have := hinj q
      exact sheafWholeSpaceSectionsComplexNat_exactAt_of_injective.{u, w} X (Z.X q) p.toNat
        (by omega)
  inducesIsoKernel q :=
    inducesIsoKernel_extendAugmentation ((sheafWholeSpaceSectionsComplexNat.{u, w} X).obj (Z.X q))
      ((globalSectionsAugmentation.{u, w} X).app (Z.X q))
      (globalSectionsAugmentation_comp_d.{u, w} X (Z.X q))
      (mono_globalSectionsAugmentation_app.{u, w} X (Z.X q))
      (exact_globalSectionsAugmentation.{u, w} X (Z.X q)) rfl rfl
      ((globalSectionsAlpha.{u, w} X Z).f q) rfl

variable [EnoughInjectives (Sheaf (SimplicialOpen.grothendieckTopology X) Ab.{w})]

/-- **The hypotheses of Stacks 0133 at the chosen injective resolution of a sheaf.** -/
theorem cohomologyDoubleComplexHypotheses_resolution
    (F : Sheaf (SimplicialOpen.grothendieckTopology X) Ab.{w}) :
    Hypotheses (((Sheaf.Γ (SimplicialOpen.grothendieckTopology X) Ab.{w}).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj ((ComplexShape.embeddingUpNat.extendFunctor
          (Sheaf (SimplicialOpen.grothendieckTopology X) Ab.{w})).obj
            (injectiveResolution F).cocomplex))
      (cohomologyDoubleComplex.{u, w} X F)
      (globalSectionsAlpha.{u, w} X ((ComplexShape.embeddingUpNat.extendFunctor
        (Sheaf (SimplicialOpen.grothendieckTopology X) Ab.{w})).obj
          (injectiveResolution F).cocomplex)) :=
  cohomologyDoubleComplexHypotheses.{u, w} X _ (isZero_injectiveResolutionExtend_X.{u, w} X F)
    (Stacks.CategoryTheory.Hypercovering.injective_injectiveResolutionExtend_X F)


/-- `Γ(X_Zar, -)` applied to the chosen injective resolution of a sheaf, extended by zero. -/
abbrev globalSectionsResZ (F : Sheaf (SimplicialOpen.grothendieckTopology X) Ab.{w}) :
    CochainComplex Ab.{w} ℤ :=
  ((Sheaf.Γ (SimplicialOpen.grothendieckTopology X) Ab.{w}).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj
    ((ComplexShape.embeddingUpNat.extendFunctor
      (Sheaf (SimplicialOpen.grothendieckTopology X) Ab.{w})).obj
        (injectiveResolution F).cocomplex)

/-- The morphism of `Γ`-applied resolutions attached to a morphism of sheaves, via the chosen
descent to the chosen injective resolutions.  Functorial only up to homotopy. -/
def globalSectionsResZMap {F G : Sheaf (SimplicialOpen.grothendieckTopology X) Ab.{w}} (f : F ⟶ G) :
    globalSectionsResZ.{u, w} X F ⟶ globalSectionsResZ.{u, w} X G :=
  ((Sheaf.Γ (SimplicialOpen.grothendieckTopology X) Ab.{w}).mapHomologicalComplex
    (ComplexShape.up ℤ)).map
    ((ComplexShape.embeddingUpNat.extendFunctor
      (Sheaf (SimplicialOpen.grothendieckTopology X) Ab.{w})).map
        (InjectiveResolution.desc f (injectiveResolution G) (injectiveResolution F)))

/-- A homotopy between two descents to the chosen injective resolutions induces a homotopy of the
induced morphisms of `Γ`-applied extended resolutions: sections are additive and extension by zero
carries homotopies to homotopies. -/
def globalSectionsResZHomotopy {F G : Sheaf (SimplicialOpen.grothendieckTopology X) Ab.{w}}
    {φ ψ : (injectiveResolution F).cocomplex ⟶ (injectiveResolution G).cocomplex}
    (H : Homotopy φ ψ) :
    Homotopy
      (((Sheaf.Γ (SimplicialOpen.grothendieckTopology X) Ab.{w}).mapHomologicalComplex
        (ComplexShape.up ℤ)).map
        ((ComplexShape.embeddingUpNat.extendFunctor
          (Sheaf (SimplicialOpen.grothendieckTopology X) Ab.{w})).map φ))
      (((Sheaf.Γ (SimplicialOpen.grothendieckTopology X) Ab.{w}).mapHomologicalComplex
        (ComplexShape.up ℤ)).map
        ((ComplexShape.embeddingUpNat.extendFunctor
          (Sheaf (SimplicialOpen.grothendieckTopology X) Ab.{w})).map ψ)) :=
  (Sheaf.Γ (SimplicialOpen.grothendieckTopology X) Ab.{w}).mapHomotopy
    (H.extend ComplexShape.embeddingUpNat)

/-- `globalSectionsResZMap` sends an identity to the identity in cohomology. -/
lemma homologyMap_globalSectionsResZMap_id
    (F : Sheaf (SimplicialOpen.grothendieckTopology X) Ab.{w}) (n : ℤ) :
    HomologicalComplex.homologyMap (globalSectionsResZMap.{u, w} X (𝟙 F)) n = 𝟙 _ := by
  have h := (globalSectionsResZHomotopy.{u, w} X
    (InjectiveResolution.descIdHomotopy F (injectiveResolution F))).homologyMap_eq n
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id,
    HomologicalComplex.homologyMap_id] at h
  exact h

/-- `globalSectionsResZMap` is multiplicative in cohomology. -/
lemma homologyMap_globalSectionsResZMap_comp
    {F G H : Sheaf (SimplicialOpen.grothendieckTopology X) Ab.{w}} (f : F ⟶ G) (g : G ⟶ H) (n : ℤ) :
    HomologicalComplex.homologyMap (globalSectionsResZMap.{u, w} X (f ≫ g)) n =
      HomologicalComplex.homologyMap (globalSectionsResZMap.{u, w} X f) n ≫
        HomologicalComplex.homologyMap (globalSectionsResZMap.{u, w} X g) n := by
  have h := (globalSectionsResZHomotopy.{u, w} X
    (InjectiveResolution.descCompHomotopy f g (injectiveResolution F) (injectiveResolution G)
      (injectiveResolution H))).homologyMap_eq n
  rw [Functor.map_comp, Functor.map_comp, HomologicalComplex.homologyMap_comp] at h
  exact h

/-- **`H^n(Γ(X_Zar, I^•(-)))`, as a functor of the sheaf.**  The `Γ`-applied chosen resolution is
functorial only up to homotopy, but cohomology is homotopy invariant. -/
def globalSectionsResZHomologyFunctor (n : ℕ) :
    Sheaf (SimplicialOpen.grothendieckTopology X) Ab.{w} ⥤ Ab.{w} where
  obj F := (globalSectionsResZ.{u, w} X F).homology (n : ℤ)
  map f := HomologicalComplex.homologyMap (globalSectionsResZMap.{u, w} X f) (n : ℤ)
  map_id F := homologyMap_globalSectionsResZMap_id.{u, w} X F (n : ℤ)
  map_comp f g := homologyMap_globalSectionsResZMap_comp.{u, w} X f g (n : ℤ)

/-- **[Stacks, Tag 0133] at a sheaf**: `H^n(Γ(X_Zar, I^•(F))) ≅ H^n(Tot(A^{•,•}(F)))`, the
isomorphism the comparison map `comparisonMapP` induces on cohomology. -/
def simplicialTotalComparisonIso (n : ℕ)
    (F : Sheaf (SimplicialOpen.grothendieckTopology X) Ab.{w}) :
    (globalSectionsResZ.{u, w} X F).homology (n : ℤ) ≅
      ((cohomologyDoubleComplex.{u, w} X F).total (ComplexShape.up ℤ)).homology (n : ℤ) :=
  comparisonHomologyIso _ _ _ (cohomologyDoubleComplexHypotheses_resolution.{u, w} X F) (n : ℤ)

/-- **`H^n(Γ(X_Zar, I^•(-))) ≅ H^n(Tot(A^{•,•}(-)))`, naturally in the sheaf.**  At each sheaf this
is `comparisonHomologyIso`, the isomorphism the comparison map of [Stacks, Tag 0133] induces on
cohomology; its naturality is `comparisonMapP_naturality` with cohomology applied to it.  Both are
available because that comparison map is *data* and not a chosen witness of an existential. -/
def simplicialTotalComparisonNatIso (n : ℕ) :
    globalSectionsResZHomologyFunctor.{u, w} X n ≅
      simplicialFiltrationFunctor.{u, w} X (n : ℤ) ⋙ CategoryTheory.FilteredObject.forget :=
  NatIso.ofComponents (fun F => simplicialTotalComparisonIso.{u, w} X n F)
    (fun {F G} f => by
      have hsq := congrArg (fun z => HomologicalComplex.homologyMap z (n : ℤ))
        (comparisonMapP_naturality _ _ _ (cohomologyDoubleComplexHypotheses_resolution.{u, w} X F)
          (cohomologyDoubleComplexHypotheses_resolution.{u, w} X G)
          (globalSectionsResZMap.{u, w} X f)
          (cohomologyDoubleComplexMap.{u, w} X f) (globalSectionsAlpha_naturality.{u, w} X _))
      simp only [HomologicalComplex.homologyMap_comp] at hsq
      exact hsq.symm)

/-- `Γ(X_Zar, -)` applied to the chosen injective resolution of a sheaf, indexed by `ℕ`. -/
abbrev globalSectionsResNat (F : Sheaf (SimplicialOpen.grothendieckTopology X) Ab.{w}) :
    CochainComplex Ab.{w} ℕ :=
  ((Sheaf.Γ (SimplicialOpen.grothendieckTopology X) Ab.{w}).mapHomologicalComplex
    (ComplexShape.up ℕ)).obj
    (injectiveResolution F).cocomplex

/-- The morphism of `ℕ`-indexed `Γ`-applied resolutions attached to a morphism of sheaves. -/
def globalSectionsResNatMap {F G : Sheaf (SimplicialOpen.grothendieckTopology X) Ab.{w}}
    (f : F ⟶ G) :
    globalSectionsResNat.{u, w} X F ⟶ globalSectionsResNat.{u, w} X G :=
  ((Sheaf.Γ (SimplicialOpen.grothendieckTopology X) Ab.{w}).mapHomologicalComplex
    (ComplexShape.up ℕ)).map
    (InjectiveResolution.desc f (injectiveResolution G) (injectiveResolution F))

/-- Piece (a) of the comparison: in the degrees coming from `ℕ`, the cohomology of the
`ℤ`-extension is the cohomology of the original complex. -/
def globalSectionsResExtendIso (n : ℕ)
    (F : Sheaf (SimplicialOpen.grothendieckTopology X) Ab.{w}) :
    (globalSectionsResZ.{u, w} X F).homology (n : ℤ) ≅
      (globalSectionsResNat.{u, w} X F).homology n :=
  (Stacks.CategoryTheory.Hypercovering.extendUpNatMapHomologyNatIso
    (Sheaf.Γ (SimplicialOpen.grothendieckTopology X) Ab.{w}) n).app
    (injectiveResolution F).cocomplex

/-- `globalSectionsResExtendIso` is natural in the sheaf, for the chosen descent. -/
lemma globalSectionsResExtendIso_hom_naturality (n : ℕ)
    {F G : Sheaf (SimplicialOpen.grothendieckTopology X) Ab.{w}} (f : F ⟶ G) :
    HomologicalComplex.homologyMap (globalSectionsResZMap.{u, w} X f) (n : ℤ) ≫
        (globalSectionsResExtendIso.{u, w} X n G).hom =
      (globalSectionsResExtendIso.{u, w} X n F).hom ≫
        HomologicalComplex.homologyMap (globalSectionsResNatMap.{u, w} X f) n :=
  (Stacks.CategoryTheory.Hypercovering.extendUpNatMapHomologyNatIso
    (Sheaf.Γ (SimplicialOpen.grothendieckTopology X) Ab.{w}) n).hom.naturality
    (InjectiveResolution.desc f (injectiveResolution G) (injectiveResolution F))

/-- Piece (b) of the comparison: the right derived functor of sections on `X` computed by the
chosen injective resolution. -/
def globalSectionsResRightDerivedIso (n : ℕ)
    (F : Sheaf (SimplicialOpen.grothendieckTopology X) Ab.{w}) :
    (globalSectionsResNat.{u, w} X F).homology n ≅
      ((Sheaf.Γ (SimplicialOpen.grothendieckTopology X) Ab.{w}).rightDerived n).obj F :=
  ((injectiveResolution F).isoRightDerivedObj
    (Sheaf.Γ (SimplicialOpen.grothendieckTopology X) Ab.{w}) n).symm

/-- `globalSectionsResRightDerivedIso` is natural in the sheaf, for the chosen descent. -/
lemma globalSectionsResRightDerivedIso_hom_naturality (n : ℕ)
    {F G : Sheaf (SimplicialOpen.grothendieckTopology X) Ab.{w}} (f : F ⟶ G) :
    HomologicalComplex.homologyMap (globalSectionsResNatMap.{u, w} X f) n ≫
        (globalSectionsResRightDerivedIso.{u, w} X n G).hom =
      (globalSectionsResRightDerivedIso.{u, w} X n F).hom ≫
        ((Sheaf.Γ (SimplicialOpen.grothendieckTopology X) Ab.{w}).rightDerived n).map f :=
  (InjectiveResolution.isoRightDerivedObj_inv_naturality f (injectiveResolution F)
    (injectiveResolution G) _
    (InjectiveResolution.desc_commutes_zero f (injectiveResolution G)
      (injectiveResolution F)) (Sheaf.Γ (SimplicialOpen.grothendieckTopology X) Ab.{w}) n).symm

/-- **`H^n(Γ(X_Zar, I^•(-))) ≅ R^nΓ(X_Zar, -)`, naturally in the sheaf.** -/
def globalSectionsRightDerivedNatIso (n : ℕ) :
    globalSectionsResZHomologyFunctor.{u, w} X n ≅
      (Sheaf.Γ (SimplicialOpen.grothendieckTopology X) Ab.{w}).rightDerived n :=
  NatIso.ofComponents
    (fun F => globalSectionsResExtendIso.{u, w} X n F ≪≫
      globalSectionsResRightDerivedIso.{u, w} X n F)
    (fun {F G} f => by
      dsimp only [globalSectionsResZHomologyFunctor, Iso.trans_hom]
      rw [← Category.assoc, globalSectionsResExtendIso_hom_naturality.{u, w} X n f, Category.assoc,
        globalSectionsResRightDerivedIso_hom_naturality.{u, w} X n f, Category.assoc])

/-- **The convergence of Stacks 09W6, on the abutment**: the cohomology of the total complex,
which is what `simplicialFunctorialAbutment` abuts to, is `H^n(X_Zar, -) = R^nΓ(X_Zar, -)`,
naturally in the sheaf. -/
def cohomologySpectralSequence_abutmentIso (n : ℕ) :
    simplicialFiltrationFunctor.{u, w} X (n : ℤ) ⋙ CategoryTheory.FilteredObject.forget ≅
      (Sheaf.Γ (SimplicialOpen.grothendieckTopology X) Ab.{w}).rightDerived n :=
  (simplicialTotalComparisonNatIso.{u, w} X n).symm ≪≫ globalSectionsRightDerivedNatIso.{u, w} X n

/-- **Stacks 09W6, the convergence.**  The spectral sequence of a simplicial topological space,
with first page `E_1^{p,q} = H^q(X_p, F_p)`, converges to `H^{p+q}(X_Zar, F)`, functorially in the
abelian sheaf `F`: for every `n` there is a finite decreasing filtration of
`H^n(X_Zar, F) = R^nΓ(X_Zar, F)`, natural in `F`, which is the whole group in step `0` and zero in
step `n + 1`, and whose graded pieces are naturally the terms `E_∞^{p,n-p}` of the infinity page.

The filtration is the one the filtration of the total complex of `A^{q,p} = I^q(X_p)` by the
simplicial degree induces on its cohomology (`simplicialFunctorialAbutment`); that cohomology is
`H^n(X_Zar, F)` by `cohomologySpectralSequence_abutmentIso`. -/
@[stacks 09W6 "convergence to H^{p+q}(X_Zar, F), functorially in the abelian sheaf"]
def cohomologySpectralSequence_abutment :
    FunctorialFirstQuadrantAbutsTo (cohomologySpectralSequence.{u, w} X)
      (fun n => (Sheaf.Γ (SimplicialOpen.grothendieckTopology X) Ab.{w}).rightDerived n) :=
  (simplicialFunctorialAbutment.{u, w} X).ofIsoAbutment
    (cohomologySpectralSequence_abutmentIso.{u, w} X)

end AbutmentIsCohomology

end Stacks.Topology.Simplicial

end
