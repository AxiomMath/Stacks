module

public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedSectionsDegeneration
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedSectionsRowAcyclic
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightAcyclicComposite
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightAcyclicFiniteProduct
public import StacksFrontier.AlgebraicGeometry.DerivedAcyclic.Pushforward
public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.LocalCohomologyVanishingDegrees
public import StacksFrontier.AlgebraicGeometry.RelativeCechComplex.HypercoveringBaseChange
public import StacksFrontier.AlgebraicGeometry.RelativeCechComplex.HypercoveringComparison
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.PiDiagramProduct

/-!
# The complex of pushforwards along a hypercovering computes the derived direct image

Let `f : X ⟶ S` be a morphism of schemes and let `K = (I, {U_i})` be a hypercovering of `X` by
opens, finite in every simplicial degree, such that every `f_i = f|_{U_i} : U_i ⟶ S` is an affine
morphism.  For a quasi-coherent `𝒪_X`-module `𝓕` the complex

`𝓚⁼ = ( ∏_{i ∈ I₀} f_{i,*}𝓕|_{U_i} ⟶ ∏_{i ∈ I₁} f_{i,*}𝓕|_{U_i} ⟶ ⋯ )`

represents `Rf_*𝓕` in `D⁺(𝒪_S)`.  This is the argument of [Stacks, Tag 01XN]:  the comparison map
`𝓚⁼(K, f, -) ⟶ Rf_*` of [Stacks, Tag 09VX] is an isomorphism at an injective module, and it is
an isomorphism at `𝓕` as soon as every degreewise functor
`M ↦ ∏_{i ∈ I_n} f_{i,*}(M|_{U_i})` is right acyclic at `𝓕` ([Stacks, Tag 0133] read along the
rows of the double complex).  That functor is a finite product of the composites
`M ↦ f_{i,*}(M|_{U_i})`, restriction to an open is exact and preserves injectives, and an affine
morphism has no higher direct images on quasi-coherent modules, so each factor is right acyclic
at `𝓕`.

Base change then gives the tag.  For `g : S' ⟶ S` with `X' = X ×_S S'`, the inverse image `g^*𝓚⁼`
is the same complex for the base changed hypercovering `K'` of `X'`, whose members
`U'_i = U_i ×_S S'` again have affine structure morphisms to `S'`;  so it represents `Rf'_*𝓕'` by
the first part, applied on `X'`.  At the hypotheses of the tag a hypercovering with all these
properties exists, whose members are moreover affine, which makes the terms of `𝓚⁼`
quasi-coherent.

## Main definitions

* `memberFunctor`:  the functor `M ↦ f_{i,*}(M|_{U_i})` attached to a member of `K`.
* `rowFunctorIso`:  the degree `n` term of `𝓚⁼(K, f, -)`, as a functor of the module, is the
  pointwise product of the `memberFunctor`s of the members of `K_n`.
* `universalPushforwardComplexOfQuasiSeparated`:  **[Stacks, Tag 01XN]**.

## Main results

* `rightAcyclic_pullback_comp_pushforward`:  `M ↦ (U.ι ≫ f)_*(M|_U)` is right acyclic at every
  quasi-coherent module when `U.ι ≫ f` is affine.
* `rightAcyclic_rowFunctor`:  every degreewise functor of `𝓚⁼(K, f, -)` is right acyclic at a
  quasi-coherent module.
* `nonempty_hypercoveringPushforwardComplexIso`:  `𝓚⁼(K, f, 𝓕) ≅ Rf_*𝓕` in `D⁺(𝒪_S)`.
* `nonempty_baseChangeIso`:  `g^*𝓚⁼(K, f, 𝓕) ≅ Rf'_*𝓕'` in `D⁺(𝒪_{S'})` for every `g`.

## Implementation notes

The comparison map of [Stacks, Tag 09VX] is produced by an existential statement (it depends on
a choice of functorial injective resolution), so the isomorphisms here are stated as `Nonempty`
and the data fields of `UniversalPushforwardComplex` are filled by choice.

The complex `hypercoveringPushforwardComplex f K` takes a quasi-coherent module, while the
comparison machinery needs the same complex as a functor on all modules,
`hypercoveringPushforwardComplexAll f K`.  The two agree definitionally on a quasi-coherent
module, but the kernel cannot check that equality as a single `rfl` within its budget; it is
assembled from small definitional steps (`hypercoveringPushforwardComplex_obj_obj_eq_all`).  For
the same reason the isomorphism of bounded below complexes between the two spellings and its
composites in `D⁺` are kept in separate declarations rather than inlined into one term.

## References

* [Stacks Project, Tag 01XN](https://stacks.math.columbia.edu/tag/01XN)
* [Stacks Project, Tag 09VX](https://stacks.math.columbia.edu/tag/09VX)
* [Stacks Project, Tag 0133](https://stacks.math.columbia.edu/tag/0133)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial TopologicalSpace
open AlgebraicGeometry AlgebraicGeometry.Scheme.Modules

-- The derived categories here are the standard ones, as in
-- `Stacks.AlgebraicGeometry.UniversalPushforward.UniversalPushforwardComplex`;  the priority
-- keeps the locally small model of `StacksFrontier.Homology.DerivedCategory.LocallySmall` from
-- being chosen for a universe-polymorphic statement.
attribute [local instance 2000] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

universe u

namespace Stacks.AlgebraicGeometry.UniversalPushforward

open Stacks.CategoryTheory.Hypercovering StacksDraft.DerivedSectionsComparison
open Stacks.AlgebraicGeometry.RelativeCech

variable {X S : Scheme.{u}}

/-! ### One member of the hypercovering -/

/-- **Restriction to an open subscheme preserves injective modules** ([Stacks, Tag 01E1]),
read on the inverse image along the inclusion of the open. -/
instance pullback_opensι_preservesInjectiveObjects (U : X.Opens) :
    (Scheme.Modules.pullback U.ι).PreservesInjectiveObjects where
  injective_obj {M} hM :=
    haveI := hM
    Injective.of_iso ((Scheme.Modules.restrictFunctorIsoPullback U.ι).app M)
      (Stacks.Perfect.LocalCohomologyDegrees.injective_restrictFunctor_obj U M)

/-- **Restricting to an open with affine structure morphism and pushing forward is right acyclic
at a quasi-coherent module.**  Restriction to `U` is exact and preserves injectives, so the
higher right derived functors of the composite at `M` are those of `(U.ι ≫ f)_*` at `M|_U`, which
vanish because `U.ι ≫ f` is affine and `M|_U` is quasi-coherent. -/
theorem rightAcyclic_pullback_comp_pushforward (U : X.Opens) (f : X ⟶ S)
    [IsAffineHom (U.ι ≫ f)] (M : X.Modules) [M.IsQuasicoherent] :
    (Scheme.Modules.pullback U.ι ⋙ Scheme.Modules.pushforward (U.ι ≫ f)).rightAcyclic M := by
  have := AlgebraicGeometry.pullback_preservesFiniteLimits_of_isOpenImmersion U.ι
  have : ((Scheme.Modules.pullback U.ι).obj M).IsQuasicoherent :=
    Stacks.Modules.isQuasicoherent_pullback _ M inferInstance
  exact CategoryTheory.Functor.rightAcyclic_comp_of_exact_of_preservesInjectiveObjects
    (Scheme.Modules.pullback U.ι) (Scheme.Modules.pushforward (U.ι ≫ f)) M
    (Stacks.Cohomology.AffineComparison.rightAcyclic_pushforward_of_isAffineHom (U.ι ≫ f)
      ((Scheme.Modules.pullback U.ι).obj M))

/-- **The functor `M ↦ f_{i,*}(M|_{U_i})` of a member `U_i` of `K_n`.** -/
abbrev memberFunctor (f : X ⟶ S)
    (K : SimplicialObject (FormalCoproduct.{u} (Over (⊤ : Opens X)))) (n : ℕ)
    (i : (K.obj (op ⦋n⦌)).I) : X.Modules ⥤ S.Modules :=
  Scheme.Modules.pullback (Scheme.Opens.ι (X := X) ((K.obj (op ⦋n⦌)).obj i).left) ⋙
    Scheme.Modules.pushforward (Scheme.Opens.ι (X := X) ((K.obj (op ⦋n⦌)).obj i).left ≫ f)

/-- **The coefficient presheaf evaluated at an open `U`, as a functor of the module, is
`M ↦ (U.ι ≫ f)_*(M|_U)`.**  This is `pushforwardPresheafAll_comp_evaluation_top` at an arbitrary
object of `Over (⊤ : Opens X)`. -/
theorem pushforwardPresheafAll_comp_evaluation (f : X ⟶ S) (A : Over (⊤ : Opens X)) :
    pushforwardPresheafAll f ⋙ (evaluation (Over (⊤ : Opens X))ᵒᵖ S.Modules).obj (op A) =
      Scheme.Modules.pullback (Scheme.Opens.ι (X := X) A.left) ⋙
        Scheme.Modules.pushforward (Scheme.Opens.ι (X := X) A.left ≫ f) :=
  rfl

/-! ### The degreewise functors -/

/-- The degree `n` term of the sections complex, unfolded:  the pointwise product of the
evaluations at the members of `K_n`. -/
theorem levelFunctor_eq_piDiagram (K : SimplicialObject (FormalCoproduct.{u} (Over (⊤ : Opens X))))
    (n : ℕ) :
    levelFunctor.{u} (A := S.Modules) K n =
      piDiagram (fun i : (K.obj (op ⦋n⦌)).I ↦
        (evaluation (Over (⊤ : Opens X))ᵒᵖ S.Modules).obj (op ((K.obj (op ⦋n⦌)).obj i))) ⋙
        lim :=
  rfl

/-- **The degree `n` term of `𝓚⁼(K, f, -)` is the product of the `memberFunctor`s**, naturally in
the module:  `M ↦ ∏_{i ∈ I_n} f_{i,*}(M|_{U_i})`, the product taken pointwise. -/
def rowFunctorIso (f : X ⟶ S)
    (K : SimplicialObject (FormalCoproduct.{u} (Over (⊤ : Opens X)))) (n : ℕ) :
    rowFunctor (hypercoveringPushforwardComplexAll f K) (n : ℤ) ≅
      piDiagram (memberFunctor f K n) ⋙ lim :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (pushforwardPresheafAll f) (Functor.associator _ _ _) ≪≫
    Functor.isoWhiskerLeft (pushforwardPresheafAll f)
      (Functor.isoWhiskerLeft (FormalCoproduct.cochainComplexFunctor K)
        (ComplexShape.embeddingUpNat.extendFunctorCompEvalIso S.Modules (i := n) (by simp))) ≪≫
    Functor.isoWhiskerLeft (pushforwardPresheafAll f)
      (cochainComplexFunctorCompEvalIso.{u} K n) ≪≫
    eqToIso (congrArg (fun G ↦ pushforwardPresheafAll f ⋙ G) (levelFunctor_eq_piDiagram K n)) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (compPiDiagramIso _ _) lim ≪≫
    eqToIso (congrArg (fun F ↦ piDiagram F ⋙ lim)
      (funext fun i ↦ pushforwardPresheafAll_comp_evaluation f ((K.obj (op ⦋n⦌)).obj i)))

/-- **Every degreewise functor of `𝓚⁼(K, f, -)` is right acyclic at a quasi-coherent module**,
when `K` is finite in every degree and every `f_i` is affine:  it is a finite product of the
`memberFunctor`s, each right acyclic at a quasi-coherent module by
`rightAcyclic_pullback_comp_pushforward`. -/
theorem rightAcyclic_rowFunctor (f : X ⟶ S)
    (K : SimplicialObject (FormalCoproduct.{u} (Over (⊤ : Opens X))))
    (hfin : ∀ n : ℕ, Finite (K.obj (op ⦋n⦌)).I)
    (hK : ∀ (n : ℕ) (i : (K.obj (op ⦋n⦌)).I),
      IsAffineHom (Scheme.Opens.ι (X := X) ((K.obj (op ⦋n⦌)).obj i).left ≫ f))
    (M : X.Modules) [M.IsQuasicoherent] (n : ℕ) :
    (rowFunctor (hypercoveringPushforwardComplexAll f K) (n : ℤ)).rightAcyclic M := by
  classical
  have := Fintype.ofFinite (K.obj (op ⦋n⦌)).I
  have : ∀ i, PreservesFiniteLimits (memberFunctor f K n i) := fun i ↦ by
    have := AlgebraicGeometry.pullback_preservesFiniteLimits_of_isOpenImmersion
      (Scheme.Opens.ι (X := X) ((K.obj (op ⦋n⦌)).obj i).left)
    dsimp only [memberFunctor]; infer_instance
  have : PreservesFiniteLimits (rowFunctor (hypercoveringPushforwardComplexAll f K) (n : ℤ)) :=
    preservesFiniteLimits_of_natIso (rowFunctorIso f K n).symm
  exact CategoryTheory.Functor.rightAcyclic_of_isoPi _ (memberFunctor f K n)
    (rowFunctorIso f K n ≪≫ piDiagramCompLimIsoPi _) M
    (fun i ↦ have := hK n i; rightAcyclic_pullback_comp_pushforward _ f M)

/-! ### The two spellings of the complex -/

private theorem flip_comp_whiskeringRight_obj {I J A B : Type*} [Category* I] [Category* J]
    [Category* A] [Category* B] (K : I ⥤ J ⥤ A) (G : A ⥤ B) (j : J) :
    (K ⋙ (Functor.whiskeringRight J A B).obj G).flip.obj j = K.flip.obj j ⋙ G :=
  rfl

private theorem comp_whiskeringLeft_obj {I J J' B : Type*} [Category* I] [Category* J]
    [Category* J'] [Category* B] (P : I ⥤ J ⥤ B) (H : J' ⥤ J) (i : I) :
    (P ⋙ (Functor.whiskeringLeft J' J B).obj H).obj i = H ⋙ P.obj i :=
  rfl

/-- The coefficient presheaf on all modules is the presheaf of monads followed by the direct
image, restricted to the opens of `X`. -/
theorem pushforwardPresheafAll_obj_eq_relativeMonad (f : X ⟶ S) (M : X.Modules) :
    (pushforwardPresheafAll f).obj M =
      (opensOverTop X).op ⋙ ((relativeMonad X).flip.obj M ⋙ pushforward f) :=
  (comp_whiskeringLeft_obj _ _ M).trans
    (congrArg (fun P ↦ (opensOverTop X).op ⋙ P) (flip_comp_whiskeringRight_obj _ _ M))

private theorem qcohModule_eq
    (F : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory) :
    RelativeCechBaseChange.qcohModule F = F.obj :=
  rfl

/-- **On a quasi-coherent module the two coefficient presheaves agree**, as presheaves on the
opens of `X`. -/
theorem pushforwardPresheaf_obj_eq_pushforwardPresheafAll (f : X ⟶ S)
    (F : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory) :
    (pushforwardPresheaf f).obj F = (pushforwardPresheafAll f).obj F.obj :=
  (Stacks.AlgebraicGeometry.HypercoveringBaseChange.pushforwardPresheaf_obj_eq f F).trans
    ((congrArg (fun M ↦ (opensOverTop X).op ⋙ ((relativeMonad X).flip.obj M ⋙ pushforward f))
      (qcohModule_eq F)).trans (pushforwardPresheafAll_obj_eq_relativeMonad f F.obj).symm)

/-- **On a quasi-coherent module the two complexes agree**:  `hypercoveringPushforwardComplex`
is `hypercoveringPushforwardComplexAll` at the underlying module. -/
theorem hypercoveringPushforwardComplex_obj_obj_eq_all (f : X ⟶ S)
    (K : SimplicialObject (FormalCoproduct.{u} (Over (⊤ : Opens X))))
    (F : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory) :
    ((hypercoveringPushforwardComplex f K).obj F).obj =
      (hypercoveringPushforwardComplexAll f K).obj F.obj :=
  (hypercoveringPushforwardComplex_obj_obj f K F).trans
    ((congrArg (fun P ↦ ((FormalCoproduct.cochainComplexFunctor K).obj P).extend
        ComplexShape.embeddingUpNat) (pushforwardPresheaf_obj_eq_pushforwardPresheafAll f F)).trans
      (hypercoveringPushforwardComplexAll_obj f K F.obj).symm)

private theorem ι_obj_hypercoveringPushforwardComplex (f : X ⟶ S)
    (K : SimplicialObject (FormalCoproduct.{u} (Over (⊤ : Opens X))))
    (F : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory) :
    (CochainComplex.Plus.ι S.Modules).obj ((hypercoveringPushforwardComplex f K).obj F) =
      ((hypercoveringPushforwardComplex f K).obj F).obj :=
  rfl

private theorem ι_obj_tPlus (f : X ⟶ S)
    (K : SimplicialObject (FormalCoproduct.{u} (Over (⊤ : Opens X)))) (M : X.Modules) :
    (CochainComplex.Plus.ι S.Modules).obj ((TPlus (hypercoveringPushforwardComplexAll f K)
        (isZero_hypercoveringPushforwardComplexAll_obj_X f K)).obj M) =
      (hypercoveringPushforwardComplexAll f K).obj M :=
  rfl

private theorem ι_obj_hypercoveringPushforwardComplex_eq_tPlus (f : X ⟶ S)
    (K : SimplicialObject (FormalCoproduct.{u} (Over (⊤ : Opens X))))
    (F : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory) :
    (CochainComplex.Plus.ι S.Modules).obj ((hypercoveringPushforwardComplex f K).obj F) =
      (CochainComplex.Plus.ι S.Modules).obj ((TPlus (hypercoveringPushforwardComplexAll f K)
        (isZero_hypercoveringPushforwardComplexAll_obj_X f K)).obj F.obj) :=
  (ι_obj_hypercoveringPushforwardComplex f K F).trans
    ((hypercoveringPushforwardComplex_obj_obj_eq_all f K F).trans (ι_obj_tPlus f K F.obj).symm)

/-- **The two spellings of `𝓚⁼(K, f, 𝓕)` are isomorphic as bounded below complexes.** -/
theorem nonempty_hypercoveringPushforwardComplexIsoTPlus (f : X ⟶ S)
    (K : SimplicialObject (FormalCoproduct.{u} (Over (⊤ : Opens X))))
    (F : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory) :
    Nonempty ((hypercoveringPushforwardComplex f K).obj F ≅
      (TPlus (hypercoveringPushforwardComplexAll f K)
        (isZero_hypercoveringPushforwardComplexAll_obj_X f K)).obj F.obj) :=
  ⟨(CochainComplex.Plus.fullyFaithfulι S.Modules).preimageIso
    (eqToIso (ι_obj_hypercoveringPushforwardComplex_eq_tPlus f K F))⟩

/-! ### The derived direct image -/

/-- **The comparison map of [Stacks, Tag 09VX] is an isomorphism at a quasi-coherent module**,
for a hypercovering finite in every degree whose members have affine structure morphisms to `S`.
Its rows are resolutions by `rightAcyclic_rowFunctor`, so
`StacksDraft.DerivedSectionsComparison.exists_comparison_of_hypotheses` applies. -/
theorem nonempty_tPlusIsoRightDerivedFunctorPlus (f : X ⟶ S)
    (K : SimplicialObject (FormalCoproduct.{u} (Over (⊤ : Opens X))))
    (hK : IsHypercovering (Opens.pretopology ↥X) K)
    (hfin : ∀ n : ℕ, Finite (K.obj (op ⦋n⦌)).I)
    (hKa : ∀ (n : ℕ) (i : (K.obj (op ⦋n⦌)).I),
      IsAffineHom (Scheme.Opens.ι (X := X) ((K.obj (op ⦋n⦌)).obj i).left ≫ f))
    (M : X.Modules) [M.IsQuasicoherent] :
    Nonempty (DerivedCategory.Plus.Q.obj ((TPlus (hypercoveringPushforwardComplexAll f K)
        (isZero_hypercoveringPushforwardComplexAll_obj_X f K)).obj M) ≅
      (Scheme.Modules.pushforward f).rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj M)) := by
  obtain ⟨Rs, ν, hν, hGE⟩ :=
    exists_resolutionData_isStrictlyGE X.Modules (hasFunctorialInjectiveEmbeddings_Modules X)
  obtain ⟨α, -, -, hα⟩ := exists_comparison_of_hypotheses Rs ν (Scheme.Modules.pushforward f)
    (hypercoveringPushforwardComplexAll f K)
    (fun M ↦ (hypercoveringAugAll f K).app M)
    (fun {_ _} φ ↦ hypercoveringAugAll_naturality f K φ)
    (isZero_hypercoveringPushforwardComplexAll_obj_X f K)
    (fun I hI ↦ @quasiIso_hypercoveringAugAll_app_of_injective _ _ f K hK I hI) hν
    (fun M ↦ M.IsQuasicoherent)
    (fun M hM ↦ hypotheses_flip_of_rightAcyclic_nonneg Rs ν _ M
      (isZero_hypercoveringPushforwardComplexAll_obj_X f K) hν (hGE M)
      (fun n ↦ have := hM; rightAcyclic_rowFunctor f K hfin hKa M n))
  have := hα M inferInstance
  exact ⟨asIso (α.app M)⟩

/-- **The complex of pushforwards along a hypercovering represents `Rf_*𝓕`.**  For a
hypercovering `K` of `X`, finite in every degree, all of whose members have affine structure
morphisms `f_i : U_i ⟶ S`, and a quasi-coherent `𝒪_X`-module `𝓕`,
`𝓚⁼(K, f, 𝓕) ≅ Rf_*𝓕` in `D⁺(𝒪_S)`. -/
theorem nonempty_hypercoveringPushforwardComplexIso (f : X ⟶ S)
    (K : SimplicialObject (FormalCoproduct.{u} (Over (⊤ : Opens X))))
    (hK : IsHypercovering (Opens.pretopology ↥X) K)
    (hfin : ∀ n : ℕ, Finite (K.obj (op ⦋n⦌)).I)
    (hKa : ∀ (n : ℕ) (i : (K.obj (op ⦋n⦌)).I),
      IsAffineHom (Scheme.Opens.ι (X := X) ((K.obj (op ⦋n⦌)).obj i).left ≫ f))
    (F : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory) :
    Nonempty (DerivedCategory.Plus.Q.obj ((hypercoveringPushforwardComplex f K).obj F) ≅
      (Scheme.Modules.pushforward f).rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj F.obj)) := by
  have : F.obj.IsQuasicoherent := F.property
  obtain ⟨e₁⟩ := nonempty_hypercoveringPushforwardComplexIsoTPlus f K F
  obtain ⟨e₂⟩ := nonempty_tPlusIsoRightDerivedFunctorPlus f K hK hfin hKa F.obj
  exact ⟨DerivedCategory.Plus.Q.mapIso e₁ ≪≫ e₂⟩

/-! ### Base change -/

/-- **An open whose structure morphism is affine stays so after base change.**  For a cartesian
square `X' ⟶ X`, `X' ⟶ S'` over `f : X ⟶ S`, `g : S' ⟶ S`, the open `(g')^{-1}U` of `X'` is
`U ×_S S'`, so `(g')^{-1}U ⟶ S'` is a base change of `U ⟶ S`. -/
theorem isAffineHom_preimage_ι_comp {X' S' : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ S'}
    {f : X ⟶ S} {g : S' ⟶ S} (hw : IsPullback g' f' f g) (U : X.Opens)
    [IsAffineHom (U.ι ≫ f)] : IsAffineHom ((g' ⁻¹ᵁ U).ι ≫ f') :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    ((isPullback_morphismRestrict g' U).paste_vert hw) inferInstance

open HypercoveringBaseChange in
/-- **The inverse image of `𝓚⁼(K, f, 𝓕)` along any `g : S' ⟶ S` represents `Rf'_*𝓕'`.**  The
inverse image is the complex of the base changed hypercovering on `X' = X ×_S S'`
(`HypercoveringBaseChange.baseChangeHypercoveringPushforwardComplexIso`), which is again a
hypercovering, finite in every degree, with affine structure morphisms to `S'`;  so
`nonempty_hypercoveringPushforwardComplexIso` applies on `X'`.  Nothing is assumed about `g`. -/
theorem nonempty_baseChangeIso (f : X ⟶ S)
    (K : SimplicialObject (FormalCoproduct.{u} (Over (⊤ : Opens X))))
    (hK : IsHypercovering (Opens.pretopology ↥X) K)
    (hfin : ∀ n : ℕ, Finite (K.obj (op ⦋n⦌)).I)
    (hKa : ∀ (n : ℕ) (i : (K.obj (op ⦋n⦌)).I),
      IsAffineHom (Scheme.Opens.ι (X := X) ((K.obj (op ⦋n⦌)).obj i).left ≫ f))
    (F : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory)
    {S' : Scheme.{u}} (g : S' ⟶ S) :
    Nonempty (DerivedCategory.Plus.Q.obj ((Scheme.Modules.pullback g).mapCochainComplexPlus.obj
        ((hypercoveringPushforwardComplex f K).obj F)) ≅
      (canonicalBaseChangeDiagram f F g).derivedPushforward') := by
  have hw := IsPullback.of_hasPullback f g
  obtain ⟨e⟩ := nonempty_hypercoveringPushforwardComplexIso (Limits.pullback.snd f g)
    (K ⋙ mapFormalCoproduct.{u} (baseChangeOpens (Limits.pullback.fst f g)))
    (AlgebraicGeometry.isHypercovering_baseChange (Limits.pullback.fst f g) K hK) hfin
    (fun n i ↦ have := hKa n i; isAffineHom_preimage_ι_comp hw _)
    (RelativeCechBaseChange.pullbackQcohObj (Limits.pullback.fst f g) F)
  exact ⟨DerivedCategory.Plus.Q.mapIso
      (baseChangeHypercoveringPushforwardComplexIso hw K hfin hKa F) ≪≫ e⟩

/-! ### The statement of the tag -/

/-- **Stacks Project, Tag 01XN.**  Let `f : X ⟶ S` be a quasi-compact and quasi-separated
morphism of schemes with `S` quasi-compact and separated, and let `𝓕` be a quasi-coherent
`𝒪_X`-module.  There is a bounded below complex `𝓚⁼` of quasi-coherent `𝒪_S`-modules such that
for every morphism `g : S' ⟶ S` the complex `g^*𝓚⁼` represents `Rf'_*𝓕'` in `D⁺(S')`, with the
notation of the cartesian square of [Stacks, Tag 02KF].

The complex is `𝓚⁼(K, f, 𝓕) = ( ∏_{i ∈ I₀} f_{i,*}𝓕|_{U_i} ⟶ ∏_{i ∈ I₁} f_{i,*}𝓕|_{U_i} ⟶ ⋯ )`
for a hypercovering `K = (I, {U_i})` of `X` finite in every degree by affine opens
(`exists_finite_affine_hypercovering_isAffineHom`, [Stacks, Tag 01H7]); its terms are
quasi-coherent because each `f_i : U_i ⟶ S` is affine, `S` being separated, and the
base-change isomorphisms are `nonempty_baseChangeIso`. -/
@[stacks 01XN]
def universalPushforwardComplexOfQuasiSeparated (f : X ⟶ S) [QuasiCompact f]
    [QuasiSeparated f] [CompactSpace S] [S.IsSeparated]
    (F : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory) :
    UniversalPushforwardComplex f F where
  complex := (hypercoveringPushforwardComplex f
    (exists_finite_affine_hypercovering_isAffineHom f).choose).obj F
  isQuasicoherent := hypercoveringPushforwardComplex_obj_isQuasicoherent f _
    (fun n ↦ ⟨((exists_finite_affine_hypercovering_isAffineHom f).choose_spec.2 n).1,
      fun i ↦ (((exists_finite_affine_hypercovering_isAffineHom f).choose_spec.2 n).2 i).1⟩) F
  baseChangeIso g := (nonempty_baseChangeIso f _
    (exists_finite_affine_hypercovering_isAffineHom f).choose_spec.1
    (fun n ↦ ((exists_finite_affine_hypercovering_isAffineHom f).choose_spec.2 n).1)
    (fun n i ↦ (((exists_finite_affine_hypercovering_isAffineHom f).choose_spec.2 n).2 i).2)
    F g).some

/-- **[Stacks, Tag 01XN] as an existence statement.** -/
theorem nonempty_universalPushforwardComplex (f : X ⟶ S) [QuasiCompact f]
    [QuasiSeparated f] [CompactSpace S] [S.IsSeparated]
    (F : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory) :
    Nonempty (UniversalPushforwardComplex f F) :=
  ⟨universalPushforwardComplexOfQuasiSeparated f F⟩

end Stacks.AlgebraicGeometry.UniversalPushforward

end
