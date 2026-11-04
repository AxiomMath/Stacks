module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ConstantSheafIsom
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ConstantSheafIsomSupplement
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocallyConstantSheafHomSupplement
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocallyConstantWeakSerre
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocallyConstantWeakSerreSupplement
public import StacksFrontier.AlgebraicGeometry.Descent.OpenSubsetFpqc
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocallyConstantPullback.InverseImageFiniteTypeLocallyConstant
public import StacksFrontier.AlgebraicGeometry.ProEtale.Cohomology.EpsilonEssentialImage
public import StacksFrontier.AlgebraicGeometry.ProEtale.Cohomology.TorsorComparison
public import StacksFrontier.AlgebraicGeometry.ProEtale.WeaklyContractible.LocallyConstantTrivialization
public import StacksFrontier.AlgebraicGeometry.Topologies.Fpqc.FiniteFlatAffineFamily
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.IsomTorsor
public import StacksFrontier.CategoryTheory.Sites.SheafPullbackEssentialImage
public import StacksFrontier.AlgebraicGeometry.ProEtale.ConstructibleConstantSheaf
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Locally constant sheaves on the étale and the pro-étale site

Let `X` be a scheme, `Λ` a ring and `ε : X_proétale → X_étale` the morphism of sites given by the
inclusion of the small étale site into the small pro-étale site. The inverse image `ε⁻¹` of sheaves
of `Λ`-modules restricts to an equivalence between the locally constant sheaves of `Λ`-modules of
finite presentation on `X_étale` and those on `X_proétale` (Stacks 099Y).

That `ε⁻¹` carries locally constant sheaves to locally constant sheaves with the same values is the
compatibility of inverse images with restriction to slices and with constant sheaves. It is fully
faithful because the unit `𝒜 ⟶ ε_* ε⁻¹ 𝒜` is an isomorphism (Stacks 099T). The content is essential
surjectivity, which follows the source. Let `F` be locally constant of finite presentation on
`X_proétale` and `U` an affine object of `X_étale`. A pro-étale covering of `U` trivializing `F`
is refined to a finite covering `{V_k → U}` by affine objects, over which `F ≅ M̲_k`. Two members
with points over the same point of `U` have isomorphic values, since constant sheaves which are
isomorphic over a nonempty object have isomorphic values (Stacks 093T (2)); as pro-étale coverings
are fpqc coverings, the points of `U` over which the value is `M` form an open subset `U_M`
(Stacks 03N0), and the `U_M` cover `U`. Over `U_M` the sheaf `Isom(F, M̲)` is a pseudo-torsor under
`Aut(M̲)`, the constant sheaf on `Aut_Λ(M)` (Stacks 093T (2)), which comes from `X_étale`, and it
has sections pro-étale locally. By the relative form of Stacks 099X it has sections étale locally,
so `F` is étale locally isomorphic to a constant sheaf. A sheaf of sets on `X_proétale` which is
étale locally isomorphic to the inverse image of an étale sheaf lies in the essential image of
`ε⁻¹` (`CategoryTheory.Presheaf.isIso_counit_of_isLocallyFromImage`), and the étale sheaf it comes
from is then étale locally constant, since isomorphisms between inverse images descend.

## Main definitions

* `AlgebraicGeometry.ProEtale.etaleInverseImageLocallyConstant`: `ε⁻¹` as a functor between the
  categories of locally constant sheaves of `Λ`-modules of finite presentation.

## Main results

* `AlgebraicGeometry.ProEtale.exists_covering_iso_constantSheaf`: a locally constant sheaf of
  `Λ`-modules of finite presentation on `X_proétale` is étale locally constant.
* `AlgebraicGeometry.ProEtale.etaleInverseImage_essImage_of_isFinitePresentationLocallyConstant`:
  such a sheaf lies in the essential image of `ε⁻¹`.
* `AlgebraicGeometry.ProEtale.isFinitePresentationLocallyConstantModuleSheaf_etaleInverseImage` and
  `AlgebraicGeometry.ProEtale.isFinitePresentationLocallyConstantModuleSheaf_of_etaleInverseImage`:
  an étale sheaf is locally constant of finite presentation exactly when its inverse image is.
* `AlgebraicGeometry.ProEtale.isEquivalence_etaleInverseImageLocallyConstant`: **Stacks 099Y**.
* `isFinitePresentationLocallyConstantModuleSheaf_iff_isFiniteTypeLocallyConstantModuleSheaf`:
  in the namespace `Stacks.ConstantSheaf`, over a Noetherian ring the finite presentation and
  finite type conditions agree.

## Implementation notes

`Λ` is a commutative ring: in the source all rings are commutative. Locally constant of finite
presentation is `Stacks.ConstantSheaf.IsFinitePresentationLocallyConstantModuleSheaf`, local
isomorphism with the constant sheaf on a finitely presented module; for a locally constant sheaf
this is finite presentation of the sheaf (Stacks 093N (2)). The sheaves of modules have sections in
the universe `max (u + 1) v w`, as for `AlgebraicGeometry.Scheme.etaleInverseImage`.

## References

* [Stacks Project, Tag 099Y](https://stacks.math.columbia.edu/tag/099Y)
* [Stacks Project, Tag 099X](https://stacks.math.columbia.edu/tag/099X)
* [Stacks Project, Tag 099T](https://stacks.math.columbia.edu/tag/099T)
* [Stacks Project, Tag 093T](https://stacks.math.columbia.edu/tag/093T)
* [Stacks Project, Tag 03N0](https://stacks.math.columbia.edu/tag/03N0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.ConstantSheaf

universe w v u x

/-! ### Local constancy of finite presentation along a morphism of sites -/

namespace Stacks.ConstantSheaf

section FinitePresentation

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) (Λ : Type w) [CommRing Λ]

/-- **A single covering of a final object suffices for local constancy of finite presentation.**
This is `Stacks.ConstantSheaf.isFiniteTypeLocallyConstant_of_cover` with finite generation of
the values replaced by finite presentation. -/
@[sga "4 IX 2.0" "partial"]
theorem isFinitePresentationLocallyConstantModuleSheaf_of_cover [HasPullbacks C] {T : C}
    (hT : IsTerminal T) (F : Sheaf J (ModuleCat.{max u v x} Λ))
    {I : Type*} {X : I → C} {f : ∀ i, X i ⟶ T} (hf : Sieve.ofArrows X f ∈ J T)
    (hc : ∀ i, ∃ E : ModuleCat.{max u v x} Λ, Module.FinitePresentation Λ E ∧ Nonempty
      ((constantSheaf (J.over (X i)) (ModuleCat.{max u v x} Λ)).obj E ≅
        (J.overPullback (ModuleCat.{max u v x} Λ) (X i)).obj F)) :
    IsFinitePresentationLocallyConstantModuleSheaf J Λ F := by
  intro U
  refine ⟨Σ V : C, {g : V ⟶ U // (Sieve.pullback (hT.from U) (Sieve.ofArrows X f)).arrows g},
    fun p => p.1, fun p => p.2.1,
    sieve_ofArrows_arrows_mem J _ (J.pullback_stable (hT.from U) hf), fun p => ?_⟩
  have h1 : (Sieve.ofArrows X f).arrows (p.2.1 ≫ hT.from U) := p.2.2
  rw [hT.hom_ext (p.2.1 ≫ hT.from U) (hT.from p.1)] at h1
  obtain ⟨i, h, -⟩ := (Sieve.mem_ofArrows_iff _ _ _).mp h1
  obtain ⟨E, hE, ⟨c⟩⟩ := hc i
  exact ⟨E, hE, ⟨constantIsoOverPullbackOfMap J (ModuleCat.{max u v x} Λ) h F E c⟩⟩

/-- **Inverse image preserves local constancy of finite presentation.** The inverse image of a
locally constant sheaf of modules of finite presentation along a continuous left exact functor of
sites carrying a final object to a final object is locally constant of finite presentation, with
the same values. This is `Stacks.ConstantSheaf.isFiniteTypeLocallyConstant_sheafPullback` with
finite generation replaced by finite presentation. -/
theorem isFinitePresentationLocallyConstantModuleSheaf_sheafPullback {D : Type u} [Category.{v} D]
    (K : GrothendieckTopology D) [HasFiniteLimits C] [HasFiniteLimits D]
    (G : C ⥤ D) [G.IsContinuous J K] [PreservesFiniteLimits G]
    [(G.sheafPushforwardContinuous (ModuleCat.{max u v x} Λ) J K).IsRightAdjoint]
    [∀ X : C, (Over.post (X := X) G).IsContinuous (J.over X) (K.over (G.obj X))]
    [∀ X : C, ((Over.post (X := X) G).sheafPushforwardContinuous (ModuleCat.{max u v x} Λ)
      (J.over X) (K.over (G.obj X))).IsRightAdjoint]
    (hG : CoverPreserving J K G) {T : C} (hGT : IsTerminal (G.obj T))
    (F : Sheaf J (ModuleCat.{max u v x} Λ))
    (hF : IsFinitePresentationLocallyConstantModuleSheaf J Λ F) :
    IsFinitePresentationLocallyConstantModuleSheaf K Λ
      ((G.sheafPullback (ModuleCat.{max u v x} Λ) J K).obj F) := by
  obtain ⟨I, X, f, hf, hc⟩ := hF T
  refine isFinitePresentationLocallyConstantModuleSheaf_of_cover K Λ hGT _
    (sieve_ofArrows_map_mem J K G hG hf) fun i => ?_
  obtain ⟨E, hE, ⟨c⟩⟩ := hc i
  exact ⟨E, hE, ⟨constantIsoOverPullbackSheafPullback J K (ModuleCat.{max u v x} Λ) G (X i) F E c⟩⟩

/-- **Over a Noetherian ring, local constancy of finite type is local constancy of finite
presentation**: a finitely generated module over a Noetherian ring is finitely presented. -/
theorem isFinitePresentationLocallyConstantModuleSheaf_iff_isFiniteTypeLocallyConstantModuleSheaf
    [IsNoetherianRing Λ] (F : Sheaf J (ModuleCat.{max u v x} Λ)) :
    IsFinitePresentationLocallyConstantModuleSheaf J Λ F ↔
      IsFiniteTypeLocallyConstantModuleSheaf.{v, u, x, w} J Λ F := by
  refine ⟨fun hF U => ?_, fun hF U => ?_⟩
  · obtain ⟨I, V, f, hf, h⟩ := hF U
    refine ⟨I, V, f, hf, fun i => ?_⟩
    obtain ⟨E, hE, e⟩ := h i
    exact ⟨E, (inferInstance : Module.Finite Λ E), e⟩
  · obtain ⟨I, V, f, hf, h⟩ := hF U
    refine ⟨I, V, f, hf, fun i => ?_⟩
    obtain ⟨E, hE, e⟩ := h i
    have : Module.Finite Λ E := hE
    exact ⟨E, Module.finitePresentation_of_finite Λ E, e⟩

end FinitePresentation

end Stacks.ConstantSheaf

namespace AlgebraicGeometry.ProEtale

variable {X : Scheme.{u}} (Λ : Type v) [CommRing Λ]

/-! ### Sheafification of sheaves of modules on the two sites and their slices -/

/-- Sheaves of `Λ`-modules on `X_proétale` admit sheafification. -/
local instance hasSheafify_proEt_moduleCat :
    HasSheafify (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) v w} Λ) :=
  hasSheafify_moduleCat.{u + 1, u, max v w, v} _ _

/-- Sheaves of `Λ`-modules on the slice of `X_proétale` over `U` admit sheafification. -/
local instance hasSheafify_proEt_over_moduleCat (U : X.ProEt) :
    HasSheafify ((Scheme.ProEt.topology X).over U) (ModuleCat.{max (u + 1) v w} Λ) :=
  hasSheafify_moduleCat.{u + 1, u, max v w, v} _ _

/-- Sheaves of `Λ`-modules on `X_étale` admit sheafification. -/
local instance hasSheafify_etale_moduleCat :
    HasSheafify X.smallEtaleTopology (ModuleCat.{max (u + 1) v w} Λ) :=
  hasSheafify_moduleCat.{u + 1, u, max v w, v} _ _

/-- Sheaves of `Λ`-modules on the slice of `X_étale` over `U` admit sheafification. -/
local instance hasSheafify_etale_over_moduleCat (U : X.Etale) :
    HasSheafify (X.smallEtaleTopology.over U) (ModuleCat.{max (u + 1) v w} Λ) :=
  hasSheafify_moduleCat.{u + 1, u, max v w, v} _ _

/-! ### Constant sheaves on overlapping objects -/

/-- The structure morphism of an object of `X_proétale` over `U` is weakly étale. -/
private theorem weaklyEtale_left {U Y : X.ProEt} (f : Y ⟶ U) : WeaklyEtale f.left :=
  MorphismProperty.of_postcomp _ _ U.hom U.prop
    (by rw [MorphismProperty.Over.w f]; exact Y.prop)

/-- **Trivializations of one sheaf over overlapping objects have isomorphic values.** Let `F` be
a sheaf of `Λ`-modules on `X_proétale` which is constant with finitely presented value `M₁` over
`Y₁` and with finitely presented value `M₂` over `Y₂`. If `Y₁` and `Y₂` have points with the same
image in an object `U` over which both lie, then `M₁ ≅ M₂`: over the nonempty fibre product
`Y₁ ×_U Y₂` the constant sheaves on `M₁` and `M₂` are both isomorphic to `F`. -/
theorem nonempty_linearEquiv_of_apply_eq {U Y₁ Y₂ : X.ProEt} (f₁ : Y₁ ⟶ U) (f₂ : Y₂ ⟶ U)
    (F : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) v w} Λ))
    (M₁ M₂ : ModuleCat.{max (u + 1) v w} Λ)
    [Module.FinitePresentation Λ M₁] [Module.FinitePresentation Λ M₂]
    (c₁ : (constantSheaf ((Scheme.ProEt.topology X).over Y₁)
        (ModuleCat.{max (u + 1) v w} Λ)).obj M₁ ≅
      ((Scheme.ProEt.topology X).overPullback (ModuleCat.{max (u + 1) v w} Λ) Y₁).obj F)
    (c₂ : (constantSheaf ((Scheme.ProEt.topology X).over Y₂)
        (ModuleCat.{max (u + 1) v w} Λ)).obj M₂ ≅
      ((Scheme.ProEt.topology X).overPullback (ModuleCat.{max (u + 1) v w} Λ) Y₂).obj F)
    (y₁ : Y₁.left) (y₂ : Y₂.left) (h : f₁.left y₁ = f₂.left y₂) :
    Nonempty ((M₁ : Type (max (u + 1) v w)) ≃ₗ[Λ] (M₂ : Type (max (u + 1) v w))) := by
  obtain ⟨z, -, -⟩ := Scheme.Pullback.exists_preimage_pullback y₁ y₂ h
  have : WeaklyEtale f₂.left := weaklyEtale_left f₂
  have : WeaklyEtale Y₁.hom := Y₁.prop
  let V : X.ProEt := Scheme.ProEt.mk (pullback.fst f₁.left f₂.left ≫ Y₁.hom)
  let a : V ⟶ Y₁ := MorphismProperty.Over.homMk (pullback.fst f₁.left f₂.left) rfl trivial
  let b : V ⟶ Y₂ := MorphismProperty.Over.homMk (pullback.snd f₁.left f₂.left) (by
    show pullback.snd f₁.left f₂.left ≫ Y₂.hom = pullback.fst f₁.left f₂.left ≫ Y₁.hom
    rw [← MorphismProperty.Over.w f₁, ← MorphismProperty.Over.w f₂, pullback.condition_assoc])
    trivial
  have hV : (⊥ : Sieve V) ∉ Scheme.ProEt.topology X V :=
    Scheme.ProEt.bot_notMem_topology_of_nonempty (V := V) z
  exact nonempty_linearEquiv_of_iso.{u + 1, u, v, max v w} (Scheme.ProEt.topology X) Λ M₁ M₂ hV
    (((overPullbackConstantSheafIso (Scheme.ProEt.topology X) _ V).app M₁).symm ≪≫
      constantIsoOverPullbackOfMap _ _ a F M₁ c₁ ≪≫
      (constantIsoOverPullbackOfMap _ _ b F M₂ c₂).symm ≪≫
      (overPullbackConstantSheafIso (Scheme.ProEt.topology X) _ V).app M₂)

/-! ### Decomposing an affine object by the values of a trivialization -/

/-- Let `E` be a finite family of affine objects of `X_proétale` covering an affine object of
`X_étale`, over each member of which `F` is constant with a finitely presented value `M k`. The
points of `U` over which the value is isomorphic to `M k₀` form an open subset `V`, whose inverse
image in a member `E.X k` is everything if `M k ≅ M k₀` and nothing otherwise. -/
theorem exists_opens_preimage_eq {U : X.Etale} [IsAffine U.left]
    (E : PreZeroHypercover.{u} (X.etaleToProetale.obj U)) [Finite E.I₀]
    (hE : E.sieve₀ ∈ Scheme.ProEt.topology X (X.etaleToProetale.obj U))
    (hEa : ∀ k, IsAffine (E.X k).left)
    (F : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) v w} Λ))
    (M : E.I₀ → ModuleCat.{max (u + 1) v w} Λ) [∀ k, Module.FinitePresentation Λ (M k)]
    (c : ∀ k, (constantSheaf ((Scheme.ProEt.topology X).over (E.X k))
        (ModuleCat.{max (u + 1) v w} Λ)).obj (M k) ≅
      ((Scheme.ProEt.topology X).overPullback (ModuleCat.{max (u + 1) v w} Λ) (E.X k)).obj F)
    (k₀ : E.I₀) :
    ∃ V : U.left.Opens,
      (∀ k, Nonempty ((M k : Type (max (u + 1) v w)) ≃ₗ[Λ] (M k₀ : Type (max (u + 1) v w))) →
        (E.f k).left ⁻¹ᵁ V = ⊤) ∧
      (∀ k, ¬ Nonempty ((M k : Type (max (u + 1) v w)) ≃ₗ[Λ] (M k₀ : Type (max (u + 1) v w))) →
        (E.f k).left ⁻¹ᵁ V = ⊥) := by
  classical
  obtain ⟨n, ⟨eqv⟩⟩ := Finite.exists_equiv_fin E.I₀
  have hfpqc : Presieve.ofArrows (fun k => (E.X k).left) (fun k => (E.f k).left) ∈
      Scheme.fpqcPrecoverage U.left := by
    refine Scheme.ofArrows_mem_fpqcPrecoverage_of_finite_index inferInstance _ _ hEa
      (fun k => (weaklyEtale_left (E.f k)).flat)
      fun x => ?_
    obtain ⟨V, g, hg, y, rfl⟩ := Scheme.ProEt.exists_mem_range_of_mem_topology hE x
    obtain ⟨_, a, _, ⟨k⟩, rfl⟩ := hg
    exact ⟨k, a.left y, rfl⟩
  let W : ∀ k, (E.X k).left.Opens := fun k =>
    if Nonempty ((M k : Type (max (u + 1) v w)) ≃ₗ[Λ] (M k₀ : Type (max (u + 1) v w)))
      then ⊤ else ⊥
  obtain ⟨V, hV, -⟩ := existsUnique_isOpen_preimage_eq_of_mem_fpqcPrecoverage _ _ hfpqc W
    fun k l => by
      ext z
      obtain ⟨e⟩ := nonempty_linearEquiv_of_apply_eq Λ (E.f k) (E.f l) F (M k) (M l) (c k) (c l)
        (pullback.fst (E.f k).left (E.f l).left z) (pullback.snd (E.f k).left (E.f l).left z)
        ((Scheme.Hom.comp_apply _ _ z).symm.trans ((congrArg (fun h => h z)
          (pullback.condition (f := (E.f k).left) (g := (E.f l).left))).trans
            (Scheme.Hom.comp_apply _ _ z)))
      by_cases hk : Nonempty ((M k : Type (max (u + 1) v w)) ≃ₗ[Λ] (M k₀ : Type (max (u + 1) v w)))
      · have hl : Nonempty ((M l : Type (max (u + 1) v w)) ≃ₗ[Λ]
            (M k₀ : Type (max (u + 1) v w))) := ⟨e.symm.trans hk.some⟩
        simp [W, hk, hl]
      · have hl : ¬ Nonempty ((M l : Type (max (u + 1) v w)) ≃ₗ[Λ]
            (M k₀ : Type (max (u + 1) v w))) := fun ⟨e'⟩ => hk ⟨e.trans e'⟩
        simp [W, hk, hl]
  exact ⟨V, fun k hk => (hV k).trans (by simp [W, hk]), fun k hk => (hV k).trans (by simp [W, hk])⟩

/-! ### The sheaf of isomorphisms to a constant sheaf comes from the étale site -/

/-- The inverse image of a constant sheaf of sets on `X_étale` is the constant sheaf of sets on
`X_proétale` with the same value. -/
def etaleTypeInverseImageConstantSheafIso :
    constantSheaf X.smallEtaleTopology (Type (max (u + 1) v)) ⋙
      Scheme.etaleTypeInverseImage.{v} X ≅
        constantSheaf (Scheme.ProEt.topology X) (Type (max (u + 1) v)) :=
  Functor.isoWhiskerLeft _ (Functor.sheafPullbackConstruction.sheafPullbackIso X.etaleToProetale
      (Type (max (u + 1) v)) X.smallEtaleTopology (Scheme.ProEt.topology X)).symm ≪≫
    sheafPullbackConstantSheafIso X.etaleToProetale _ _ _ (isTerminalEtaleFinal X)
      (isTerminalEtaleToProetaleObjEtaleFinal X) (Iso.refl _)

/-- **The sheaf of isomorphisms between constant sheaves comes from the étale site.** For
finitely presented `Λ`-modules `M` and `N`, the sheaf of sets `Isom(M̲, N̲)` on `X_proétale` lies
in the essential image of `ε⁻¹`: by Tag 093T (2) it is the constant sheaf on `M ≃ₗ[Λ] N`, which is
the inverse image of the constant sheaf on `X_étale`. -/
theorem sheafIsom_constantSheaf_mem_essImage (M N : ModuleCat.{max (u + 1) v w} Λ)
    [Module.FinitePresentation Λ M] [Module.FinitePresentation Λ N] :
    (Scheme.etaleTypeInverseImage.{max v w} X).essImage
      (sheafIsom (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) v w} Λ)
        ((constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) v w} Λ)).obj M)
        ((constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) v w} Λ)).obj N)) :=
  ⟨(constantSheaf X.smallEtaleTopology (Type (max (u + 1) v w))).obj
      ((M : Type (max (u + 1) v w)) ≃ₗ[Λ] (N : Type (max (u + 1) v w))),
    ⟨(etaleTypeInverseImageConstantSheafIso.{max v w}).app _ ≪≫
      constantSheafIsomIso.{u + 1, u, v, max v w} (Scheme.ProEt.topology X) Λ M N⟩⟩

/-! ### Locally constant pro-étale sheaves are étale locally constant -/

/-- A sheaf of sets on `X_proétale` has a section over an object with empty underlying scheme. -/
theorem nonempty_obj_of_isEmpty (T : Sheaf (Scheme.ProEt.topology X) (Type (max (u + 1) v)))
    {V : X.ProEt} (hV : IsEmpty V.left) : Nonempty (T.obj.obj (op V)) :=
  ⟨(Sheaf.isTerminalOfBotCover T V (Scheme.ProEt.bot_mem_topology_of_isEmpty V hV)).from
    PUnit PUnit.unit⟩

/-- The sieve of objects `W` of `X_étale` over `U` such that `F` is constant over `W` with a
finitely presented value. -/
private def constantValueSieve
    (F : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) v w} Λ)) (U : X.Etale) :
    Sieve U where
  arrows W _ := ∃ M : ModuleCat.{max (u + 1) v w} Λ, Module.FinitePresentation Λ M ∧
    Nonempty ((constantSheaf ((Scheme.ProEt.topology X).over (X.etaleToProetale.obj W))
      (ModuleCat.{max (u + 1) v w} Λ)).obj M ≅
        ((Scheme.ProEt.topology X).overPullback (ModuleCat.{max (u + 1) v w} Λ)
          (X.etaleToProetale.obj W)).obj F)
  downward_closed := fun {_ _ _} ⟨M, hM, ⟨e⟩⟩ h =>
    ⟨M, hM, ⟨constantIsoOverPullbackOfMap _ _ (X.etaleToProetale.map h) F M e⟩⟩

/-- **A locally constant sheaf of finite presentation on `X_proétale` is étale locally constant,
over an affine object.** Let `F` be a locally constant sheaf of `Λ`-modules of finite presentation
on `X_proétale` and let `U` be an affine object of `X_étale`. Then `U` has an étale covering by
objects `W` over which `F` is constant with a finitely presented value.

This is the argument of Stacks 099Y. A pro-étale covering of `U` trivializing `F` is refined by a
finite one by affine objects; the points of `U` over which the value is a given module form an open
subset (`AlgebraicGeometry.ProEtale.exists_opens_preimage_eq`), and over it `Isom(F, M̲)` is a
pseudo-torsor under `Aut(M̲)`, which comes from `X_étale`, with sections pro-étale locally. By the
relative form of Stacks 099X (`AlgebraicGeometry.ProEtale.exists_covering_nonempty`) it has
sections étale locally. -/
theorem exists_covering_iso_constantSheaf_of_isAffine
    (F : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) v w} Λ))
    (hF : IsFinitePresentationLocallyConstantModuleSheaf.{u + 1, u, v, max v w}
      (Scheme.ProEt.topology X) Λ F)
    (U : X.Etale) [IsAffine U.left] :
    ∃ S ∈ X.smallEtaleTopology U, ∀ ⦃W : X.Etale⦄ ⦃g : W ⟶ U⦄, S g →
      ∃ M : ModuleCat.{max (u + 1) v w} Λ, Module.FinitePresentation Λ M ∧
        Nonempty ((constantSheaf ((Scheme.ProEt.topology X).over (X.etaleToProetale.obj W))
          (ModuleCat.{max (u + 1) v w} Λ)).obj M ≅
            ((Scheme.ProEt.topology X).overPullback (ModuleCat.{max (u + 1) v w} Λ)
              (X.etaleToProetale.obj W)).obj F) := by
  classical
  let Jp := Scheme.ProEt.topology X
  let A := ModuleCat.{max (u + 1) v w} Λ
  obtain ⟨I, V, f, hcov, hV⟩ := hF (X.etaleToProetale.obj U)
  have : IsAffine (X.etaleToProetale.obj U).left := ‹IsAffine U.left›
  obtain ⟨E, hfin, hE, hle, hEa⟩ := exists_indEtale_covering_le _ hcov
  have hk : ∀ k, ∃ M : A, Module.FinitePresentation Λ M ∧
      Nonempty ((constantSheaf (Jp.over (E.X k)) A).obj M ≅ (Jp.overPullback A (E.X k)).obj F) := by
    intro k
    obtain ⟨i, a, -⟩ := (Sieve.mem_ofArrows_iff V f (E.f k)).mp (hle _ (E.sieve₀_f k))
    obtain ⟨M, hM, ⟨c⟩⟩ := hV i
    exact ⟨M, hM, ⟨constantIsoOverPullbackOfMap _ _ a F M c⟩⟩
  choose M hM c using hk
  have := hM
  have hEa' : ∀ k, IsAffine (E.X k).left := fun k => (hEa k).1
  choose O hO₁ hO₂ using fun k₀ =>
    exists_opens_preimage_eq Λ E hE hEa' F M (fun k => (c k).some) k₀
  -- the étale covering of `U` by the open subsets `O k₀`
  let Uk (k₀ : E.I₀) : X.Etale := Scheme.Etale.mk ((O k₀).ι ≫ U.hom)
  let ιk (k₀ : E.I₀) : Uk k₀ ⟶ U := MorphismProperty.Over.homMk (O k₀).ι rfl
  have hR : Sieve.ofArrows Uk ιk ∈ X.smallEtaleTopology U := by
    rw [Scheme.ofArrows_mem_smallEtaleTopology_iff]
    refine Set.eq_univ_of_forall fun x => ?_
    obtain ⟨Y, h, hh, y, rfl⟩ := Scheme.ProEt.exists_mem_range_of_mem_topology hE x
    obtain ⟨_, a, _, ⟨k⟩, rfl⟩ := hh
    refine Set.mem_iUnion.2 ⟨k, ?_⟩
    show _ ∈ Set.range (O k).ι
    rw [Scheme.Opens.range_ι]
    have hmem : (a.left y) ∈ (E.f k).left ⁻¹ᵁ O k := by
      rw [hO₁ k k ⟨LinearEquiv.refl Λ _⟩]; trivial
    exact hmem
  refine ⟨constantValueSieve Λ F U, X.smallEtaleTopology.transitive hR _ fun W g hg => ?_,
    fun W g hg => hg⟩
  obtain ⟨_, h, _, ⟨k₀⟩, rfl⟩ := hg
  rw [Sieve.pullback_comp]
  refine X.smallEtaleTopology.pullback_stable h ?_
  -- over `O k₀`, the pseudo-torsor `Isom(F, M̲)` has sections étale locally
  let Mc := (constantSheaf Jp A).obj (M k₀)
  let T := sheafIsomPseudoTorsor Jp A F Mc
  obtain ⟨F₀, ⟨e₀⟩⟩ := sheafIsom_constantSheaf_mem_essImage Λ (M k₀) (M k₀) (X := X)
  -- the pseudo-torsor has sections pro-étale locally over `O k₀`
  have hT : ∃ S ∈ Jp (X.etaleToProetale.obj (Uk k₀)), ∀ ⦃V : X.ProEt⦄
      ⦃f : V ⟶ X.etaleToProetale.obj (Uk k₀)⦄, S f → Nonempty (T.presheaf.obj (op V)) := by
    refine ⟨Sieve.pullback (X.etaleToProetale.map (ιk k₀)) E.sieve₀,
      Jp.pullback_stable _ hE, fun V' g' hg' => ?_⟩
    obtain ⟨Y, a, _, ⟨l⟩, hal⟩ := hg'
    by_cases hl : Nonempty ((M l : Type (max (u + 1) v w)) ≃ₗ[Λ] (M k₀ : Type (max (u + 1) v w)))
    · let e₁ := constantIsoOverPullbackOfMap _ _ a F (M l) (c l).some
      let e₂ : (constantSheaf (Jp.over V') A).obj (M l) ≅
          (constantSheaf (Jp.over V') A).obj (M k₀) :=
        (constantSheaf (Jp.over V') A).mapIso hl.some.toModuleIso
      let e := e₁.symm ≪≫ e₂ ≪≫ (overPullbackConstantSheafIso Jp A V').app (M k₀)
      exact ⟨⟨e.hom, (inferInstance : IsIso e.hom)⟩⟩
    · refine nonempty_obj_of_isEmpty.{max v w, u} (⟨T.presheaf, T.isSheaf⟩ : Sheaf Jp _)
        ⟨fun v => ?_⟩
      have h₁ : (a.left v) ∈ (E.f l).left ⁻¹ᵁ O k₀ := by
        have h₂ : (E.f l).left (a.left v) = (O k₀).ι (g'.left v) := by
          have := congrArg (fun φ : V' ⟶ X.etaleToProetale.obj U => φ.left v) hal
          change (a.left ≫ (E.f l).left) v = (g'.left ≫ (O k₀).ι) v at this
          exact ((Scheme.Hom.comp_apply _ _ v).symm.trans this).trans (Scheme.Hom.comp_apply _ _ v)
        have h₃ : (O k₀).ι (g'.left v) ∈ (O k₀ : Set U.left) := by
          rw [← Scheme.Opens.range_ι]; exact ⟨_, rfl⟩
        show (E.f l).left (a.left v) ∈ O k₀
        rw [h₂]
        exact h₃
      rw [hO₂ k₀ l hl] at h₁
      exact h₁
  obtain ⟨S', hS', hs'⟩ := exists_covering_nonempty.{max v w, u} (sheafAut Jp A Mc) F₀
    ((sheafToPresheaf _ _).mapIso e₀.symm) T (Uk k₀) hT
  refine X.smallEtaleTopology.superset_covering (fun W' g' hg' => ?_) hS'
  obtain ⟨s⟩ := hs' hg'
  have : IsIso s.1 := s.2
  exact ⟨M k₀, inferInstance, ⟨(overPullbackConstantSheafIso Jp A _).app (M k₀) ≪≫
    (asIso s.1).symm⟩⟩

/-- **A locally constant sheaf of finite presentation on `X_proétale` is étale locally constant.**
Every object `U` of `X_étale` has an étale covering by objects over which `F` is constant with a
finitely presented value: the affine objects cover `U`
(`AlgebraicGeometry.ProEtale.exists_covering_iso_constantSheaf_of_isAffine`). -/
theorem exists_covering_iso_constantSheaf
    (F : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) v w} Λ))
    (hF : IsFinitePresentationLocallyConstantModuleSheaf.{u + 1, u, v, max v w}
      (Scheme.ProEt.topology X) Λ F)
    (U : X.Etale) :
    ∃ S ∈ X.smallEtaleTopology U, ∀ ⦃W : X.Etale⦄ ⦃g : W ⟶ U⦄, S g →
      ∃ M : ModuleCat.{max (u + 1) v w} Λ, Module.FinitePresentation Λ M ∧
        Nonempty ((constantSheaf ((Scheme.ProEt.topology X).over (X.etaleToProetale.obj W))
          (ModuleCat.{max (u + 1) v w} Λ)).obj M ≅
            ((Scheme.ProEt.topology X).overPullback (ModuleCat.{max (u + 1) v w} Λ)
              (X.etaleToProetale.obj W)).obj F) := by
  refine ⟨constantValueSieve Λ F U, ?_, fun W g hg => hg⟩
  obtain ⟨P, hP, hPaff⟩ := exists_affine_presieve_mem_smallEtaleTopology X U
  refine X.smallEtaleTopology.transitive hP _ fun W f hf => ?_
  obtain ⟨W', h, f', hf', rfl⟩ := hf
  have : IsAffine W'.left := hPaff f' hf'
  obtain ⟨S', hS', hs'⟩ := exists_covering_iso_constantSheaf_of_isAffine Λ F hF W'
  rw [Sieve.pullback_comp]
  exact X.smallEtaleTopology.pullback_stable h
    (X.smallEtaleTopology.superset_covering (fun V g hg => hs' hg) hS')

/-! ### Locally constant pro-étale sheaves come from the étale site -/

attribute [local instance] preservesSheafification_forget_moduleCat_of_univLE

/-- The underlying sheaf of sets of a constant sheaf of `Λ`-modules on `X_proétale` satisfies the
criterion `CategoryTheory.Presheaf.IsLocallyFromImage` for `ε`: it is the constant sheaf of sets,
which is the inverse image of the constant sheaf of sets on `X_étale`. -/
theorem isLocallyFromImage_constantSheaf (M : ModuleCat.{max (u + 1) v w} Λ) :
    Presheaf.IsLocallyFromImage X.etaleToProetale (Scheme.ProEt.topology X)
      ((sheafCompose _ (CategoryTheory.forget (ModuleCat.{max (u + 1) v w} Λ))).obj
        ((constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) v w} Λ)).obj M)).obj := by
  have := Scheme.isIso_proetaleInverseImageAdjunction_unit.{u, max v w} X
  have : RepresentablyFlat X.etaleToProetale := flat_of_preservesFiniteLimits _
  have := Scheme.hasPointwiseLeftKanExtension_etaleToProetale_type.{u, max v w} X
  have : (Scheme.ProEt.topology X).WEqualsLocallyBijective (Type (max (u + 1) v w)) :=
    wEqualsLocallyBijective_type.{u + 1, u, max (u + 1) v w} _
  refine Presheaf.IsLocallyFromImage.of_iso ((sheafToPresheaf _ _).mapIso
    ((etaleTypeInverseImageConstantSheafIso.{max v w}).app (M : Type (max (u + 1) v w)) ≪≫
      ((constantCommuteCompose (Scheme.ProEt.topology X)
        (CategoryTheory.forget (ModuleCat.{max (u + 1) v w} Λ))).app M).symm))
    (Presheaf.isLocallyFromImage_sheafPullback (u := X.etaleToProetale)
      (K := Scheme.ProEt.topology X) (J := X.smallEtaleTopology)
      ((constantSheaf X.smallEtaleTopology (Type (max (u + 1) v w))).obj
        (M : Type (max (u + 1) v w))))

/-- **A locally constant sheaf of finite presentation on `X_proétale` comes from `X_étale`.**
Its underlying sheaf of sets satisfies the criterion `CategoryTheory.Presheaf.IsLocallyFromImage`,
because it is étale locally isomorphic to a constant sheaf
(`AlgebraicGeometry.ProEtale.exists_covering_iso_constantSheaf`); hence the counit of `ε⁻¹ ⊣ ε_*`
is an isomorphism at it. -/
theorem etaleInverseImage_essImage_of_isFinitePresentationLocallyConstant
    {Λ : Type v} [CommRing Λ]
    (F : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) v w} Λ))
    (hF : IsFinitePresentationLocallyConstantModuleSheaf.{u + 1, u, v, max v w}
      (Scheme.ProEt.topology X) Λ F) :
    (Scheme.etaleInverseImage.{u, w, v} X Λ).essImage F := by
  rw [Scheme.etaleInverseImage_essImage_iff_forget]
  have := Scheme.isIso_proetaleInverseImageAdjunction_unit.{u, max v w} X
  have : RepresentablyFlat X.etaleToProetale := flat_of_preservesFiniteLimits _
  have := Scheme.hasPointwiseLeftKanExtension_etaleToProetale_type.{u, max v w} X
  have : (Scheme.ProEt.topology X).WEqualsLocallyBijective (Type (max (u + 1) v w)) :=
    wEqualsLocallyBijective_type.{u + 1, u, max (u + 1) v w} _
  let A := ModuleCat.{max (u + 1) v w} Λ
  let Q := (sheafCompose (Scheme.ProEt.topology X) (CategoryTheory.forget A)).obj F
  let adj := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous X.etaleToProetale
    (Type (max (u + 1) v w)) X.smallEtaleTopology (Scheme.ProEt.topology X)
  have hQ : Presheaf.IsLocallyFromImage X.etaleToProetale (Scheme.ProEt.topology X) Q.obj := by
    refine Presheaf.IsLocallyFromImage.of_locallyIso
      (CoverPreserving.of_isContinuous X.etaleToProetale X.smallEtaleTopology
        (Scheme.ProEt.topology X)) _
      fun W₀ => ?_
    obtain ⟨S, hS, hs⟩ := exists_covering_iso_constantSheaf Λ F hF W₀
    refine ⟨S, hS, fun W g hg => ?_⟩
    obtain ⟨M, -, ⟨c⟩⟩ := hs hg
    let c' := c.symm ≪≫ (overPullbackConstantSheafIso (Scheme.ProEt.topology X) A _).app M
    exact ⟨_, isLocallyFromImage_constantSheaf Λ M,
      ⟨Functor.isoWhiskerRight ((sheafToPresheaf _ _).mapIso c') (CategoryTheory.forget A)⟩⟩
  have := Presheaf.isIso_counit_of_isLocallyFromImage adj
    (isTerminalEtaleToProetaleObjEtaleFinal X) Q hQ
    (Presheaf.isLocallyFromImage_sheafPullback (u := X.etaleToProetale)
      (K := Scheme.ProEt.topology X) (J := X.smallEtaleTopology)
      ((X.etaleToProetale.sheafPushforwardContinuous (Type (max (u + 1) v w))
        X.smallEtaleTopology (Scheme.ProEt.topology X)).obj Q))
  exact ⟨_, ⟨asIso (adj.counit.app Q)⟩⟩

/-! ### The étale sheaves whose inverse images are locally constant -/

/-- The inverse image of a constant sheaf of `Λ`-modules on `X_étale` is the constant sheaf on
`X_proétale` with the same value. -/
def etaleInverseImageConstantSheafIso {Λ : Type v} [CommRing Λ] :
    constantSheaf X.smallEtaleTopology (ModuleCat.{max (u + 1) v w} Λ) ⋙
      Scheme.etaleInverseImage.{u, w, v} X Λ ≅
        constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) v w} Λ) :=
  Functor.isoWhiskerLeft _ (Functor.sheafPullbackConstruction.sheafPullbackIso X.etaleToProetale
      (ModuleCat.{max (u + 1) v w} Λ) X.smallEtaleTopology (Scheme.ProEt.topology X)).symm ≪≫
    sheafPullbackConstantSheafIso X.etaleToProetale _ _ _ (isTerminalEtaleFinal X)
      (isTerminalEtaleToProetaleObjEtaleFinal X) (Iso.refl _)

/-- **Isomorphisms of inverse images over an étale object descend.** Since `ε⁻¹` is fully faithful
(the unit `𝒜 ⟶ ε_* ε⁻¹ 𝒜` is invertible), an isomorphism between the restrictions of `ε⁻¹ 𝒜₁` and
`ε⁻¹ 𝒜₂` to an object `W` of `X_étale` gives an isomorphism between the restrictions of `𝒜₁` and
`𝒜₂` to `W`: over `W' ⟶ W`, the sections of `𝒜ᵢ` are those of `ε⁻¹ 𝒜ᵢ` over `W'`. -/
def overPullbackIsoOfEtaleInverseImage {Λ : Type v} [CommRing Λ] {W : X.Etale}
    {A₁ A₂ : Sheaf X.smallEtaleTopology (ModuleCat.{max (u + 1) v w} Λ)}
    (φ : ((Scheme.ProEt.topology X).overPullback (ModuleCat.{max (u + 1) v w} Λ)
        (X.etaleToProetale.obj W)).obj ((Scheme.etaleInverseImage.{u, w, v} X Λ).obj A₁) ≅
      ((Scheme.ProEt.topology X).overPullback (ModuleCat.{max (u + 1) v w} Λ)
        (X.etaleToProetale.obj W)).obj ((Scheme.etaleInverseImage.{u, w, v} X Λ).obj A₂)) :
    (X.smallEtaleTopology.overPullback (ModuleCat.{max (u + 1) v w} Λ) W).obj A₁ ≅
      (X.smallEtaleTopology.overPullback (ModuleCat.{max (u + 1) v w} Λ) W).obj A₂ :=
  let adj := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous X.etaleToProetale
    (ModuleCat.{max (u + 1) v w} Λ) X.smallEtaleTopology (Scheme.ProEt.topology X)
  (fullyFaithfulSheafToPresheaf _ _).preimageIso
    (Functor.isoWhiskerLeft (Over.forget W).op
        ((sheafToPresheaf _ _).mapIso (asIso (adj.unit.app A₁))) ≪≫
      Functor.isoWhiskerLeft (Over.post (X := W) X.etaleToProetale).op
        ((sheafToPresheaf _ _).mapIso φ) ≪≫
      (Functor.isoWhiskerLeft (Over.forget W).op
        ((sheafToPresheaf _ _).mapIso (asIso (adj.unit.app A₂)))).symm)

/-- **Inverse image preserves local constancy of finite presentation**, along `ε`. -/
theorem isFinitePresentationLocallyConstantModuleSheaf_etaleInverseImage
    {Λ : Type v} [CommRing Λ]
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{max (u + 1) v w} Λ))
    (hG : IsFinitePresentationLocallyConstantModuleSheaf.{u + 1, u, v, max v w}
      X.smallEtaleTopology Λ G) :
    IsFinitePresentationLocallyConstantModuleSheaf.{u + 1, u, v, max v w}
      (Scheme.ProEt.topology X) Λ ((Scheme.etaleInverseImage.{u, w, v} X Λ).obj G) :=
  ObjectProperty.prop_of_iso _
    ((Functor.sheafPullbackConstruction.sheafPullbackIso X.etaleToProetale
      (ModuleCat.{max (u + 1) v w} Λ) X.smallEtaleTopology (Scheme.ProEt.topology X)).app G)
    (Stacks.ConstantSheaf.isFinitePresentationLocallyConstantModuleSheaf_sheafPullback
      X.smallEtaleTopology Λ (Scheme.ProEt.topology X) X.etaleToProetale
      (CoverPreserving.of_isContinuous _ _ _) (isTerminalEtaleToProetaleObjEtaleFinal X) G hG)

/-- **An étale sheaf whose inverse image is locally constant of finite presentation is locally
constant of finite presentation.** The inverse image is étale locally constant
(`AlgebraicGeometry.ProEtale.exists_covering_iso_constantSheaf`), and isomorphisms of inverse
images over an étale object descend
(`AlgebraicGeometry.ProEtale.overPullbackIsoOfEtaleInverseImage`). -/
theorem isFinitePresentationLocallyConstantModuleSheaf_of_etaleInverseImage
    {Λ : Type v} [CommRing Λ]
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{max (u + 1) v w} Λ))
    (hG : IsFinitePresentationLocallyConstantModuleSheaf.{u + 1, u, v, max v w}
      (Scheme.ProEt.topology X) Λ ((Scheme.etaleInverseImage.{u, w, v} X Λ).obj G)) :
    IsFinitePresentationLocallyConstantModuleSheaf.{u + 1, u, v, max v w}
      X.smallEtaleTopology Λ G := by
  obtain ⟨S, hS, hs⟩ := exists_covering_iso_constantSheaf Λ _ hG (etaleFinal X)
  obtain ⟨K, Z, p, hp⟩ := S.exists_eq_ofArrows
  rw [hp] at hS
  refine Stacks.ConstantSheaf.isFinitePresentationLocallyConstantModuleSheaf_of_cover _ Λ
    (isTerminalEtaleFinal X) G hS fun k => ?_
  have hk : S (p k) := by rw [hp]; exact Sieve.ofArrows_mk Z p k
  obtain ⟨M, hM, ⟨c⟩⟩ := hs hk
  let A := ModuleCat.{max (u + 1) v w} Λ
  let φ : ((Scheme.ProEt.topology X).overPullback A (X.etaleToProetale.obj (Z k))).obj
        ((Scheme.etaleInverseImage.{u, w, v} X Λ).obj G) ≅
      ((Scheme.ProEt.topology X).overPullback A (X.etaleToProetale.obj (Z k))).obj
        ((Scheme.etaleInverseImage.{u, w, v} X Λ).obj
          ((constantSheaf X.smallEtaleTopology A).obj M)) :=
    c.symm ≪≫ (overPullbackConstantSheafIso (Scheme.ProEt.topology X) A _).app M ≪≫
      ((Scheme.ProEt.topology X).overPullback A _).mapIso
        ((etaleInverseImageConstantSheafIso.{w}).app M).symm
  exact ⟨M, hM, ⟨(overPullbackConstantSheafIso X.smallEtaleTopology A _).app M ≪≫
    (overPullbackIsoOfEtaleInverseImage φ).symm⟩⟩

/-! ### Stacks 099Y -/

variable (X) in
/-- The inverse image `ε⁻¹` of sheaves of `Λ`-modules, restricted to the locally constant sheaves
of finite presentation on `X_étale`, with values in the locally constant sheaves of finite
presentation on `X_proétale`. -/
def etaleInverseImageLocallyConstant (Λ : Type v) [CommRing Λ] :
    ObjectProperty.FullSubcategory (IsFinitePresentationLocallyConstantModuleSheaf.{u + 1, u, v,
        max v w} X.smallEtaleTopology Λ) ⥤
      ObjectProperty.FullSubcategory (IsFinitePresentationLocallyConstantModuleSheaf.{u + 1, u, v,
        max v w} (Scheme.ProEt.topology X) Λ) :=
  ObjectProperty.lift _ (ObjectProperty.ι _ ⋙ Scheme.etaleInverseImage.{u, w, v} X Λ)
    fun G => isFinitePresentationLocallyConstantModuleSheaf_etaleInverseImage G.obj G.property

variable (X) in
/-- **Stacks 099Y.** Let `X` be a scheme and `Λ` a ring. The inverse image `ε⁻¹` along the
inclusion of the small étale site into the small pro-étale site defines an equivalence between
the locally constant sheaves of `Λ`-modules of finite presentation on `X_étale` and those on
`X_proétale`.

Locally constant of finite presentation is
`Stacks.ConstantSheaf.IsFinitePresentationLocallyConstantModuleSheaf`: locally isomorphic to the
constant sheaf on a finitely presented module, which for a locally constant sheaf is finite
presentation (Stacks 093N (2)). -/
theorem isEquivalence_etaleInverseImageLocallyConstant (Λ : Type v) [CommRing Λ] :
    (etaleInverseImageLocallyConstant.{w, v, u} X Λ).IsEquivalence := by
  let adj := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous X.etaleToProetale
    (ModuleCat.{max (u + 1) v w} Λ) X.smallEtaleTopology (Scheme.ProEt.topology X)
  have hff := adj.fullyFaithfulLOfIsIsoUnit
  have : (Scheme.etaleInverseImage.{u, w, v} X Λ).Full := hff.full
  have : (Scheme.etaleInverseImage.{u, w, v} X Λ).Faithful := hff.faithful
  have : (ObjectProperty.ι _ ⋙ Scheme.etaleInverseImage.{u, w, v} X Λ :
      ObjectProperty.FullSubcategory (IsFinitePresentationLocallyConstantModuleSheaf.{u + 1, u, v,
        max v w} X.smallEtaleTopology Λ) ⥤ _).Full := Functor.Full.comp _ _
  have : (ObjectProperty.ι _ ⋙ Scheme.etaleInverseImage.{u, w, v} X Λ :
      ObjectProperty.FullSubcategory (IsFinitePresentationLocallyConstantModuleSheaf.{u + 1, u, v,
        max v w} X.smallEtaleTopology Λ) ⥤ _).Faithful := Functor.Faithful.comp _ _
  have : (etaleInverseImageLocallyConstant.{w, v, u} X Λ).Faithful :=
    Functor.Faithful.of_comp_iso (ObjectProperty.liftCompιIso _ _ _)
  have : (etaleInverseImageLocallyConstant.{w, v, u} X Λ).Full :=
    Functor.Full.of_comp_faithful_iso (ObjectProperty.liftCompιIso _ _ _)
  have : (etaleInverseImageLocallyConstant.{w, v, u} X Λ).EssSurj := ⟨fun F => by
    obtain ⟨G, ⟨e⟩⟩ := etaleInverseImage_essImage_of_isFinitePresentationLocallyConstant F.obj
      F.property
    exact ⟨⟨G, isFinitePresentationLocallyConstantModuleSheaf_of_etaleInverseImage G
      (ObjectProperty.prop_of_iso _ e.symm F.property)⟩, ⟨ObjectProperty.isoMk _ e⟩⟩⟩
  exact { }

end AlgebraicGeometry.ProEtale

end
