module

import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.CategoryTheory.Sites.EpiMono
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FiniteTypeKernel
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocallyConstantSerreClass
public import StacksFrontier.AlgebraicGeometry.ProEtale.WeaklyContractible.ClopenRefinement
public import StacksFrontier.AlgebraicGeometry.ProEtale.WeaklyContractible.SmallSiteSheafificationSections
public import StacksFrontier.AlgebraicGeometry.ProEtale.WeaklyContractible.SmallSiteSituation
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.Defs

/-!
# Sections and locally constant sheaves over a w-contractible affine of the pro-étale site

Let `S` be a scheme and `W` an affine object of the small pro-étale site `S_proét` whose ring
of global sections is w-contractible, for instance an affine weakly contractible object. Then

* a locally surjective morphism of sheaves on `S_proét`, with values in any concrete category
  and in any universe, is surjective on sections over `W`; so `W` is weakly contractible in the
  sense of Stacks 090L, at every value universe;
* a locally constant sheaf `F` on `S_proét` becomes constant on the members of a finite
  decomposition `W = ∐ W_i` of `W` into disjoint clopen subschemes.

Both rest on the refinement property of Stacks 098H: every covering sieve of `W` contains a
clopen decomposition of `W`.

This is the first step of the proofs of Stacks 09BZ and 09C3 ("since `X` is weakly
contractible, there exists a finite disjoint open covering `X = ∐ U_i` such that the locally
constant sheaf restricts to a constant sheaf on each `U_i`"): a covering trivializing `F` is
refined by a clopen decomposition of `W` (Stacks 098H), and the restriction of a constant sheaf
along a further morphism of the site is constant.

## Main results

* `AlgebraicGeometry.Scheme.ProEt.surjective_app_of_isWContractible`: a locally surjective
  morphism of sheaves of types is surjective on sections over `W`.
* `AlgebraicGeometry.Scheme.ProEt.surjective_app_over_of_isWContractible`: the same on the
  slice site over `W`, at its final object.
* `AlgebraicGeometry.Scheme.ProEt.surjective_app_of_isWContractible_of_concrete`: the same for
  sheaves with values in a concrete category whose forgetful functor preserves sheaves.
* `AlgebraicGeometry.Scheme.ProEt.isWeaklyContractible_of_isWContractible`: `W` is weakly
  contractible.
* `AlgebraicGeometry.Scheme.ProEt.preservesFiniteColimits_sheafSections_mk_id`: global sections of
  sheaves of modules over a weakly contractible affine scheme are exact.
* `AlgebraicGeometry.Scheme.ProEt.surjective_app_mk_id_of_isWeaklyContractibleObj`: global
  sections on `X_proét` are exact for an affine weakly contractible scheme `X`.
* `AlgebraicGeometry.Scheme.ProEt.isConstant_overPullback_of_hom`: the restriction of a sheaf
  which is constant over `U` to an object `V` mapping to `U` is constant.
* `AlgebraicGeometry.Scheme.ProEt.bijective_restrict_clopenDecomposition`: the sections of a
  sheaf over an object of `S_proét` are the families of sections over the members of a clopen
  decomposition of it.
* `AlgebraicGeometry.Scheme.ProEt.exists_clopenDecomposition_isConstant_of_isLocallyConstant`:
  a locally constant sheaf is constant on the members of a clopen decomposition of `W`.
* `Scheme.ProEt.exists_clopenDecomposition_forall_isConstant_of_isLocallyConstant`:
  the same for finitely many locally constant sheaves at once.

## References

* [Stacks Project, Tag 090L](https://stacks.math.columbia.edu/tag/090L)
* [Stacks Project, Tag 093Q](https://stacks.math.columbia.edu/tag/093Q)
* [Stacks Project, Tag 098H](https://stacks.math.columbia.edu/tag/098H)
* [Stacks Project, Tag 09BZ](https://stacks.math.columbia.edu/tag/09BZ)
* [Stacks Project, Tag 09C3](https://stacks.math.columbia.edu/tag/09C3)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite ProetaleWContractible

universe t w v' u' u

namespace AlgebraicGeometry.Scheme.ProEt

section Sections

variable {S : Scheme.{u}}

/-- A sieve on an object of `S_proét` whose underlying scheme has empty underlying space is
covering: the empty family is a pro-étale covering of such a scheme. -/
theorem bot_mem_topology_of_isEmpty (Z : S.ProEt) (hZ : IsEmpty Z.left) :
    (⊥ : Sieve Z) ∈ ProEt.topology S Z := by
  rw [← Sieve.generate_bot]
  refine Precoverage.generate_mem_toGrothendieck ?_
  show (⊥ : Presieve Z).map (ProEt.forget S ⋙ Over.forget S) ∈
    Scheme.proetalePrecoverage.coverings Z.left
  rw [Presieve.map_bot]
  exact Scheme.bot_mem_propQCPrecoverage (P := @WeaklyEtale) Z.left

/-- **Sections over a w-contractible affine are exact.** Let `W` be an affine object of
`S_proét` whose ring of global sections is w-contractible. A locally surjective morphism of
sheaves of types on `S_proét`, in any universe, is surjective on sections over `W`. -/
theorem surjective_app_of_isWContractible (W : S.ProEt) [IsAffine W.left]
    (hW : IsWContractible.{u, u} Γ(W.left, ⊤))
    {F G : Sheaf (ProEt.topology S) (Type t)} (φ : F ⟶ G) (hφ : Sheaf.IsLocallySurjective φ) :
    Function.Surjective (φ.hom.app (op W)) :=
  GrothendieckTopology.surjective_sections_of_clopenRefinements _
    (ProEt.forget S ⋙ Over.forget S) W (fun Z hZ ↦ bot_mem_topology_of_isEmpty Z hZ)
    (fun _ hf ↦ (ProEt.forget S ⋙ Over.forget S).mono_of_mono_map hf)
    (exists_clopenRefinement_of_isWContractible W hW) F G φ hφ

/-- **Sections over a w-contractible affine are exact, on its slice site.** Let `W` be an affine
object of `S_proét` whose ring of global sections is w-contractible. A locally surjective
morphism of sheaves of types on the slice site `S_proét/W`, in any universe, is surjective on
sections over the final object `W ⟶ W`. -/
theorem surjective_app_over_of_isWContractible (W : S.ProEt) [IsAffine W.left]
    (hW : IsWContractible.{u, u} Γ(W.left, ⊤))
    {F G : Sheaf ((ProEt.topology S).over W) (Type t)} (φ : F ⟶ G)
    (hφ : Sheaf.IsLocallySurjective φ) :
    Function.Surjective (φ.hom.app (op (Over.mk (𝟙 W)))) :=
  GrothendieckTopology.surjective_sections_over_of_clopenRefinements _
    (ProEt.forget S ⋙ Over.forget S) W (fun Z hZ ↦ bot_mem_topology_of_isEmpty Z hZ)
    (fun _ hf ↦ (ProEt.forget S ⋙ Over.forget S).mono_of_mono_map hf)
    (exists_clopenRefinement_of_isWContractible W hW) φ hφ

/-- **Sections over a w-contractible affine are exact**, for sheaves with values in a concrete
category `A` whose forgetful functor carries sheaves to sheaves (for instance modules or abelian
groups). A locally surjective morphism of such sheaves on `S_proét` is surjective on sections
over an affine object `W` with w-contractible ring of global sections. -/
theorem surjective_app_of_isWContractible_of_concrete (W : S.ProEt) [IsAffine W.left]
    (hW : IsWContractible.{u, u} Γ(W.left, ⊤))
    {A : Type u'} [Category.{v'} A] {FA : A → A → Type*} {CA : A → Type w}
    [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory A FA]
    [(ProEt.topology S).HasSheafCompose (CategoryTheory.forget A)]
    {F G : Sheaf (ProEt.topology S) A} (φ : F ⟶ G) (hφ : Sheaf.IsLocallySurjective φ) :
    Function.Surjective (φ.hom.app (op W)) := by
  have hφ' : Sheaf.IsLocallySurjective
      ((sheafCompose (ProEt.topology S) (CategoryTheory.forget A)).map φ) := by
    rw [← Sheaf.isLocallySurjective_sheafToPresheaf_map_iff]
    exact (Presheaf.isLocallySurjective_iff_whisker_forget _ φ.hom).mp
      ((Sheaf.isLocallySurjective_sheafToPresheaf_map_iff φ).mpr hφ)
  exact surjective_app_of_isWContractible W hW _ hφ'

/-- **An affine object of `S_proét` with w-contractible global sections is weakly
contractible** (Stacks 090L): every locally surjective morphism of sheaves of sets, valued in
the morphism universe of the site, is surjective on sections over it. -/
theorem isWeaklyContractible_of_isWContractible (W : S.ProEt) [IsAffine W.left]
    (hW : IsWContractible.{u, u} Γ(W.left, ⊤)) :
    (ProEt.topology S).IsWeaklyContractible W :=
  fun _ _ φ hφ ↦ surjective_app_of_isWContractible W hW φ hφ

/-- **Sections over a weakly contractible affine scheme are exact.** Let `X` be an affine scheme
which is weakly contractible as an object of the big pro-étale site (Stacks 090L). A locally
surjective morphism of sheaves on `X_proét` with values in a concrete category whose forgetful
functor preserves sheaves is surjective on global sections, that is, on sections over the final
object `X ⟶ X` of `X_proét`. -/
theorem surjective_app_mk_id_of_isWeaklyContractibleObj {X : Scheme.{u}} [IsAffine X]
    (hX : IsWeaklyContractibleObj X)
    {A : Type u'} [Category.{v'} A] {FA : A → A → Type*} {CA : A → Type w}
    [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory A FA]
    [(ProEt.topology X).HasSheafCompose (CategoryTheory.forget A)]
    {F G : Sheaf (ProEt.topology X) A} (φ : F ⟶ G) (hφ : Sheaf.IsLocallySurjective φ) :
    Function.Surjective (φ.hom.app (op (ProEt.mk (𝟙 X)))) :=
  have : IsAffine (ProEt.mk (𝟙 X)).left := inferInstanceAs (IsAffine X)
  surjective_app_of_isWContractible_of_concrete (ProEt.mk (𝟙 X))
    (isWContractible_of_isWeaklyContractible X hX) φ hφ

/-- **Global sections over a weakly contractible affine scheme are an exact functor** on
sheaves of modules on `X_proét`: they preserve finite limits as every evaluation functor does,
and they preserve epimorphisms because an epimorphism of sheaves of modules is locally
surjective, hence surjective on global sections
(`AlgebraicGeometry.Scheme.ProEt.surjective_app_mk_id_of_isWeaklyContractibleObj`). -/
theorem preservesFiniteColimits_sheafSections_mk_id {X : Scheme.{u}} [IsAffine X]
    (hX : IsWeaklyContractibleObj X) (R : Type (max (u + 1) w)) [Ring R] :
    PreservesFiniteColimits ((sheafSections (ProEt.topology X)
      (ModuleCat.{max (u + 1) w} R)).obj (op (ProEt.mk (𝟙 X)))) := by
  let E := (sheafSections (ProEt.topology X) (ModuleCat.{max (u + 1) w} R)).obj
    (op (ProEt.mk (𝟙 X)))
  have : E.Additive := E.additive_of_preserves_binary_products
  have : E.PreservesEpimorphisms := ⟨fun {F G} φ _ => by
    have hφ : Sheaf.IsLocallySurjective φ :=
      (Sheaf.isLocallySurjective_iff_epi' (ModuleCat.{max (u + 1) w} R) φ).2 inferInstance
    exact (ModuleCat.epi_iff_surjective _).2
      (surjective_app_mk_id_of_isWeaklyContractibleObj hX φ hφ)⟩
  have : E.PreservesHomology := Functor.preservesHomology_of_preservesEpis_and_kernels E
  exact Functor.preservesFiniteColimits_of_preservesHomology E

/-- Over an object of `S_proét` whose underlying scheme is empty, a sheaf of types has at most
one section. -/
theorem subsingleton_sections_of_isEmpty (G : Sheaf (ProEt.topology S) (Type t)) (Z : S.ProEt)
    (hZ : IsEmpty Z.left) : Subsingleton (G.obj.obj (op Z)) :=
  ⟨fun _ _ => ((isSheaf_iff_isSheaf_of_type _ G.obj).mp G.property _
    (bot_mem_topology_of_isEmpty Z hZ)).isSeparatedFor.ext fun _ _ h => h.elim⟩

/-- **Sections over a clopen decomposition.** For a finite decomposition of the underlying scheme
of an object `W` of `S_proét` into disjoint clopen subschemes `W_i`, the sections over `W` of a
sheaf of types are exactly the families of sections over the `W_i`. -/
theorem bijective_restrict_clopenDecomposition (G : Sheaf (ProEt.topology S) (Type t))
    (W : S.ProEt) {n : ℕ} {U : Fin n → Scheme.{u}} (f : (i : Fin n) → U i ⟶ W.left)
    (hdec : IsClopenDecompositionCover U f) (hf : ∀ i, WeaklyEtale (f i ≫ W.hom)) :
    Function.Bijective (fun (x : G.obj.obj (op W)) (i : Fin n) =>
      G.obj.map (clopenDecompositionHom W f hf i).op x) := by
  have hG := (isSheaf_iff_isSheaf_of_type _ G.obj).mp G.property
  have hsh := (Presieve.isSheafFor_iff_generate _).mpr
    (hG _ (sieve_ofArrows_clopenDecomposition_mem_topology W f hdec hf))
  rw [Presieve.isSheafFor_arrows_iff] at hsh
  refine (Function.bijective_iff_existsUnique _).mpr fun x => ?_
  refine (hsh x fun i j Z gi gj hij => ?_).imp fun t => ?_
  · by_cases h : i = j
    · subst h
      have : Mono (clopenDecompositionHom W f hf i) :=
        (ProEt.forget S ⋙ Over.forget S).mono_of_mono_map (hdec.openImmersion i).mono
      rw [cancel_mono] at hij
      rw [hij]
    · have : IsEmpty Z.left := ⟨fun z => by
        have h1 : (f i).base (((ProEt.forget S ⋙ Over.forget S).map gi).base z) =
            (f j).base (((ProEt.forget S ⋙ Over.forget S).map gj).base z) := by
          have := congrArg (fun g => ((ProEt.forget S ⋙ Over.forget S).map g).base z) hij
          simp only [Functor.map_comp] at this
          exact this
        exact Set.disjoint_left.mp (hdec.disjoint i j h) ⟨_, rfl⟩ ⟨_, h1.symm⟩⟩
      exact (subsingleton_sections_of_isEmpty G Z this).elim _ _
  · exact fun ⟨ht, hu⟩ => ⟨funext ht, fun t' h => hu t' fun i => congrFun h i⟩

end Sections

section LocallyConstant

variable {S : Scheme.{u}} {D : Type u'} [Category.{v'} D] [HasLimitsOfSize.{u, u + 1} D]
  [∀ U : S.ProEt, HasWeakSheafify ((ProEt.topology S).over U) D]

/-- The restriction of a sheaf on `S_proét` which is constant over `U` to an object `V` with a
morphism `V ⟶ U` is constant: restricting along `V ⟶ U` carries the constant sheaf on the
slice over `U` to the constant sheaf on the slice over `V`. -/
theorem isConstant_overPullback_of_hom {U V : S.ProEt} (g : V ⟶ U)
    (F : Sheaf (ProEt.topology S) D)
    (hF : Sheaf.IsConstant ((ProEt.topology S).over U)
      (((ProEt.topology S).overPullback D U).obj F)) :
    Sheaf.IsConstant ((ProEt.topology S).over V)
      (((ProEt.topology S).overPullback D V).obj F) := by
  obtain ⟨E, ⟨φ⟩⟩ := hF.mem_essImage
  exact ⟨E, ⟨(Stacks.ConstantSheaf.mapPullbackConstantSheafIso (ProEt.topology S) D g).app E ≪≫
    ((ProEt.topology S).overMapPullback D g).mapIso φ⟩⟩

/-- A sheaf which is constant over each `X i` is constant over every object `V` whose structure
map to `W` factors through some `g i`. -/
private theorem isConstant_overPullback_of_mem_ofArrows {W V : S.ProEt} {I : Type*}
    {X : I → S.ProEt} {g : ∀ i, X i ⟶ W} {h : V ⟶ W} (hh : (Sieve.ofArrows X g).arrows h)
    (F : Sheaf (ProEt.topology S) D)
    (hconst : ∀ i, Sheaf.IsConstant ((ProEt.topology S).over (X i))
      (((ProEt.topology S).overPullback D (X i)).obj F)) :
    Sheaf.IsConstant ((ProEt.topology S).over V)
      (((ProEt.topology S).overPullback D V).obj F) := by
  obtain ⟨j, h, -⟩ := (Sieve.mem_ofArrows_iff _ _ _).mp hh
  exact isConstant_overPullback_of_hom h F (hconst j)

/-- **A locally constant sheaf is constant on a clopen decomposition of a w-contractible
affine.** Let `W` be an affine object of `S_proét` whose ring of global sections is
w-contractible. Every locally constant sheaf on `S_proét` is constant on each member of some
finite decomposition of `W` into disjoint clopen subschemes `W_i ⟶ W`. -/
theorem exists_clopenDecomposition_isConstant_of_isLocallyConstant (W : S.ProEt)
    [IsAffine W.left] (hW : IsWContractible.{u, u} Γ(W.left, ⊤))
    (F : Sheaf (ProEt.topology S) D) [hF : Stacks.ConstantSheaf.IsLocallyConstant _ F] :
    ∃ (n : ℕ) (U : Fin n → Scheme.{u}) (f : (i : Fin n) → U i ⟶ W.left)
      (_ : IsClopenDecompositionCover U f) (hf : ∀ i, WeaklyEtale (f i ≫ W.hom)),
      ∀ i, Sheaf.IsConstant ((ProEt.topology S).over (clopenDecompositionObj W f hf i))
        (((ProEt.topology S).overPullback D (clopenDecompositionObj W f hf i)).obj F) := by
  obtain ⟨I, X, g, hcov, hconst⟩ := hF.exists_cover W
  obtain ⟨n, U, f, hdec, hf, hR⟩ :=
    exists_clopenDecomposition_of_isWContractible W hW _ hcov
  exact ⟨n, U, f, hdec, hf, fun i ↦ isConstant_overPullback_of_mem_ofArrows (hR i) F hconst⟩

/-- **Finitely many locally constant sheaves are simultaneously constant on a clopen
decomposition of a w-contractible affine.** Let `W` be an affine object of `S_proét` whose ring
of global sections is w-contractible, and let `F k`, for `k` in a finite type, be locally
constant sheaves on `S_proét`. Then there is a finite decomposition of `W` into disjoint clopen
subschemes `W_i ⟶ W` such that every `F k` is constant on every `W_i`. -/
theorem exists_clopenDecomposition_forall_isConstant_of_isLocallyConstant (W : S.ProEt)
    [IsAffine W.left] (hW : IsWContractible.{u, u} Γ(W.left, ⊤)) {ι : Type*} [Finite ι]
    (F : ι → Sheaf (ProEt.topology S) D)
    (hF : ∀ k, Stacks.ConstantSheaf.IsLocallyConstant _ (F k)) :
    ∃ (n : ℕ) (U : Fin n → Scheme.{u}) (f : (i : Fin n) → U i ⟶ W.left)
      (_ : IsClopenDecompositionCover U f) (hf : ∀ i, WeaklyEtale (f i ≫ W.hom)),
      ∀ i k, Sheaf.IsConstant ((ProEt.topology S).over (clopenDecompositionObj W f hf i))
        (((ProEt.topology S).overPullback D (clopenDecompositionObj W f hf i)).obj (F k)) := by
  choose I X g hcov hconst using fun k ↦ (hF k).exists_cover W
  obtain ⟨n, U, f, hdec, hf, hR⟩ := exists_clopenDecomposition_of_isWContractible W hW
    (⨅ k, Sieve.ofArrows (X k) (g k))
    (Stacks.SheafOfModules.FiniteTypeKernel.iInf_mem _ _ hcov)
  exact ⟨n, U, f, hdec, hf, fun i k ↦ isConstant_overPullback_of_mem_ofArrows
    ((Stacks.SheafOfModules.FiniteTypeKernel.iInf_apply _ _).mp (hR i) k) (F k) (hconst k)⟩

end LocallyConstant

end AlgebraicGeometry.Scheme.ProEt
